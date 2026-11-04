#!/usr/bin/env node
// Deterministic damage/repair and scope properties through the real editor API.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
const core = createRequire(import.meta.url)('../editors/shared/fhmEditorCore.cjs');
const binary = process.env.FHM || fileURLToPath(new URL('../.lake/build/bin/fhm', import.meta.url));
let state = 0x6e657374;
const random = n => { state ^= state << 13; state ^= state >>> 17; state ^= state << 5; return (state >>> 0) % n; };
function intExpr(depth) {
  if (!depth) return `${random(30)}`;
  const a = intExpr(depth - 1), b = intExpr(depth - 1);
  return random(2) ? `(${a} + ${b})` : `(if True then ${a} else ${b})`;
}
function cli(source, args = ['diagnose']) {
  const p = spawnSync(binary, args, { input: source, encoding: 'utf8', timeout: 8000, maxBuffer: 4 * 1024 * 1024 });
  assert.ifError(p.error); assert.equal(p.signal, null);
  return { status: p.status, payload: JSON.parse(p.stdout) };
}
const forms = [
  hole => `(${hole}, (local, outside + 1))`,
  hole => `(if True then ${hole} else (local + outside))`,
  hole => `[outside, ${hole}, local]`,
  hole => `(match [outside] with | head :: tail -> (${hole}, head + local) | [] -> (3, 4))`,
  hole => `(\\inner -> if True then ${hole} else (inner + outside))`,
  hole => `(let missing = ${hole} in let clean = outside + 1 in (clean, missing))`,
];
const damage = ['(2 + )', '(outside + )', '"outside ) ] } let phantom = 7"', '(if True then else)'];
let checks = 0;
for (let seed = 0; seed < 5; seed++) for (let form = 0; form < forms.length; form++) for (let edit = 0; edit < damage.length; edit++) {
  const id = `seed-${seed}/form-${form}/edit-${edit}`;
  const value = intExpr(2);
  const sourceFor = hole => `--- Identity documentation survives damage.\nlet keep value = value\nlet outside = True\nlet damaged outside =\n  let local = (outside + ${value}) in\n  ${forms[form](hole)}\nlet healthy = keep 7\nhealthy\n`;
  const source = sourceFor(damage[edit]);
  try {
    const { status, payload } = cli(source);
    assert.equal(status, 1);
    assert.ok(payload.diagnostics.some(d => !d.code), 'missing syntax diagnostic');
    assert.ok(!payload.diagnostics.some(d => d.code?.startsWith('internal.')), 'partial tree reached a native checker');
    assert.ok(!payload.diagnostics.some(d => d.code?.startsWith('lower.')), 'syntax holes caused lowering cascades');
    assert.ok(payload.symbols.every(s => !s.name.startsWith('$syntax/')), 'internal hole identity leaked');
    const def = name => payload.symbols.filter(s => s.def && s.name === name);
    assert.match(def('damaged')[0].type, /^type unknown/);
    assert.equal(def('local')[0].type, 'Int');
    assert.equal(def('outside').find(s => s.kind === 'param').type, 'Int');
    assert.equal(def('outside').find(s => s.kind === 'val').type, 'Bool');
    assert.equal(def('healthy')[0].type, 'Int');
    assert.equal(payload.programTy, 'Int');
    const { ranged, tokens } = core.normalizePayload(payload);
    const lines = source.split('\n');
    const useLine = lines.findIndex(line => line.startsWith('  let local'));
    const col = lines[useLine].indexOf('outside');
    const hover = core.resolveHover(ranged, useLine, col, lines[useLine], tokens);
    const target = core.resolveDefinition(ranged, useLine, col, lines[useLine], tokens);
    assert.equal(hover.type, 'Int');
    assert.deepEqual([target.startLine0, target.startCol0], [3, lines[3].indexOf('outside')]);
    const keepLine = lines.findIndex(line => line.startsWith('let healthy'));
    assert.match(core.resolveHover(ranged, keepLine, lines[keepLine].indexOf('keep'), lines[keepLine], tokens).doc, /Identity documentation/);
    const runner = cli(source, ['run', '--json']);
    assert.equal(runner.status, 1);
    assert.equal(runner.payload.stage, 'parse');
    const repaired = cli(sourceFor('2'));
    assert.equal(repaired.status, 0, JSON.stringify(repaired.payload.diagnostics));
    assert.deepEqual(repaired.payload.diagnostics, []);
    assert.ok(repaired.payload.symbols.every(s => !s.type.startsWith('type unknown') && !s.typeStatus));
    assert.equal(repaired.payload.programTy, 'Int');
    checks++;
  } catch (error) { throw new Error(`${id}\n${source}\n${error.stack}`); }
}
console.log(`PASS ${checks} generated damage/repair cases: lexical scope, clean hovers, docs/navigation, strict rejection and repair.`);

const damagedDelimiters = [
  '(1, (2 + 3)', '[1, (2 + 3], 4]', '(1, [2, 3)', '((1 + 2)]',
  '{1, 2}', '[1, } 2, 3]', '(\\x -> (x + 1)',
];
for (const body of damagedDelimiters) {
  const source = `let damaged = ${body}\nlet later=7\nlater\n`;
  const result = cli(source);
  assert.equal(result.status, 1);
  assert.ok(result.payload.diagnostics.length > 0);
  assert.ok(!result.payload.diagnostics.some(d => d.code?.startsWith('internal.')));
  assert.equal(result.payload.symbols.find(s => s.def && s.name === 'later').type, 'Int');
  assert.equal(result.payload.programTy, 'Int');
}
for (const prefix of ['(1 + )', '[1, (2 + ), 3]', '(if True then else 2)']) {
  const source = `${prefix}\nlet later=7\nlater\n`;
  const result = cli(source);
  assert.equal(result.status, 1);
  assert.equal(result.payload.symbols.find(s => s.def && s.name === 'later').type, 'Int');
  assert.equal(result.payload.programTy, 'Int');
}
const showcase = readFileSync(new URL('../scratch/error-recovery-partial-parser.fhm', import.meta.url), 'utf8');
const report = cli(showcase);
assert.equal(report.status, 1);
assert.equal(report.payload.diagnostics.filter(d => !d.code).length, 5);
assert.deepEqual(report.payload.diagnostics.filter(d => d.code).map(d => d.code), ['type.notFunction']);
assert.equal(report.payload.programTy, '(Int, Bool)');
const fixed = showcase.replace(/([1-4]) \+ /g, '$1').replace('if then', 'if True then').replace('5 True', '5');
const fixedReport = cli(fixed);
assert.equal(fixedReport.status, 0, JSON.stringify(fixedReport.payload.diagnostics));
assert.equal(cli(fixed, ['run', '--json']).payload.result, '(41, True)');
console.log('PASS unmatched/mismatched delimiter fallback and complete showcase repair.');

const unicode = 'let 🦄=True\nlet damaged 🦄 = ((2 + ), 🦄 + 1)\nlet later=7\nlater\n';
const unicodeReport = cli(unicode).payload;
assert.equal(unicodeReport.diagnostics[0].col, unicode.split('\n')[1].indexOf(')') + 1);
assert.equal(unicodeReport.symbols.find(s => s.def && s.name === '🦄' && s.kind === 'param').type, 'Int');
assert.equal(unicodeReport.symbols.find(s => s.def && s.name === '🦄' && s.kind === 'val').type, 'Bool');
console.log('PASS UTF-16 recovery spans and non-BMP lexical shadowing.');
