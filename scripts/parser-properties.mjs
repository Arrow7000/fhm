#!/usr/bin/env node
// Seeded AST generation, frozen strict-parser compatibility, and recovery invariants.
// Build: lake build fhm_parser_audit fhm
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
const binary = process.env.FHM_PARSER_AUDIT || fileURLToPath(new URL('../.lake/build/bin/fhm_parser_audit', import.meta.url));
const manifestPath = new URL('./fixtures/parser-before-partial.json', import.meta.url);
let rng = 0x4f484d32, fresh = 0;
const random = n => { rng ^= rng << 13; rng ^= rng >>> 17; rng ^= rng << 5; return (rng >>> 0) % n; };
const canonical = x => Array.isArray(x) ? x.map(canonical) : x && typeof x === 'object'
  ? Object.fromEntries(Object.keys(x).sort().map(k => [k, canonical(x[k])])) : x;
const hash = x => createHash('sha256').update(typeof x === 'string' ? x : JSON.stringify(canonical(x))).digest('hex');
function expr(depth, env = []) {
  const choice = random(depth ? 12 : 6);
  if (choice === 0) { const n = random(100); return { source: `${n}`, ast: ['int', `${n}`] }; }
  if (choice === 1) { const b = !!random(2); return { source: b ? 'True' : 'False', ast: ['bool', b] }; }
  if (choice === 2) return { source: '()', ast: ['unit'] };
  if (choice === 3) { const n = env.length ? env[random(env.length)] : 'free'; return { source: n, ast: ['var', n] }; }
  if (choice === 4) return { source: "'q'", ast: ['char', 'q'] };
  if (choice === 5) return { source: 'Nil', ast: ['ctor', 'Nil'] };
  const a = expr(depth - 1, env), b = expr(depth - 1, env);
  if (choice === 6) return { source: `(${a.source}, ${b.source})`, ast: ['pair', a.ast, b.ast] };
  if (choice === 7) return { source: `[${a.source}, ${b.source}]`, ast: ['list', [a.ast, b.ast]] };
  if (choice === 8) return { source: `((${a.source}) (${b.source}))`, ast: ['app', a.ast, b.ast] };
  if (choice === 9) { const c = expr(depth - 1, env); return { source: `(if ${a.source} then ${b.source} else ${c.source})`, ast: ['if', a.ast, b.ast, c.ast] }; }
  const name = `v${fresh++}`, body = expr(depth - 1, [...env, name]);
  if (choice === 10) return { source: `(\\${name} -> ${body.source})`, ast: ['lambda', ['name', name], null, body.ast] };
  return { source: `(let ${name} = ${a.source} in ${body.source})`, ast: ['let', name, [], [], null, a.ast, body.ast] };
}
const cases = [];
function add(id, source, kind = 'program', expected) { cases.push({ id, source, kind, expected }); }
for (let i = 0; i < 600; i++) {
  const tree = expr(1 + random(5));
  add(`tree-${i}`, tree.source, 'expr', tree.ast);
  add(`program-${i}`, `let generated = ${tree.source}\ngenerated\n`);
  add(`comments-${i}`, `(/- prefix -/ ${tree.source} /- suffix -/)`, 'expr', tree.ast);
  const positions = [...tree.source.matchAll(/[()[\],+]/g)].map(m => m.index);
  const at = positions.length ? positions[random(positions.length)] : random(tree.source.length);
  add(`delete-${i}`, tree.source.slice(0, at) + tree.source.slice(at + 1), 'expr');
  add(`damage-${i}`, `let generated = (${tree.source}, (2 + ))\nlet tail = 7\ntail\n`);
}
const templates = [
  n => `let f${n} x y = (x, y)\nf${n} 1 True\n`,
  n => `let f${n} : {item} ?same -> ?same = \\(x : item) -> x\nf${n} 7\n`,
  n => `let f${n} {a} (x : a) : a = x\nf${n} True\n`,
  n => `type T${n} a = Empty${n} | Node${n} a (T${n} a)\nlet f${n} xs = match xs with | Empty${n} -> 0 | Node${n} x rest -> x\nf${n} (Node${n} 1 Empty${n})\n`,
  n => `--- doc ${n}\nlet (x${n}, y${n}) = (1, True)\n(x${n}, y${n})\n`,
  n => `let f${n} x = g${n} x\nlet g${n} x = if True then x else f${n} x\nf${n} 1\n`,
  n => `let f${n} x =\n  let first y = second y\n      second y = (y, x)\n  in first 1\nf${n} True\n`,
  n => `let f${n} = \\((x, y) : (Int, Bool)) -> if y then x else 0\nf${n} (1, True)\n`,
  n => `let emoji${n} 🦄 = 🦄\nemoji${n} 7\n`,
  n => `let f${n} = (1 + (2 - 3))\nf${n}\n`,
  n => `let f${n} = [1, 2 + , 3]\nlet tail${n}=7\ntail${n}\n`,
  n => `let f${n} = if then 1 else 2\nlet tail${n}=7\ntail${n}\n`,
  n => `let f${n} = match [1] with | x :: xs -> (x + ) | [] -> 0\n0\n`,
  n => `let f${n} = \\(x : List) -> x\nf${n}\n`,
  n => `let f${n} = ("let fake=1", 2)\nf${n}\n`,
  n => `let f${n} = [1, (2 + ], 3]\nlet tail${n}=7\ntail${n}\n`,
];
for (let i = 0; i < 24; i++) for (let t = 0; t < templates.length; t++) add(`surface-${t}-${i}`, templates[t](i));

function run(requests) {
  const proc = spawnSync(binary, [], { input: requests.map(r => JSON.stringify(r)).join('\n') + '\n', encoding: 'utf8', timeout: 90000, maxBuffer: 128 * 1024 * 1024 });
  assert.ifError(proc.error); assert.equal(proc.status, 0, proc.stderr);
  const lines = proc.stdout.trimEnd().split('\n');
  assert.equal(lines.length, requests.length, proc.stderr);
  return lines.map(JSON.parse);
}
const results = run(cases.map(({ source, kind }) => ({ source, kind })));
for (let i = 0; i < cases.length; i++) {
  const c = cases[i], r = results[i];
  try {
    if (c.expected) { assert.equal(r.ok, true); assert.deepEqual(r.ast, c.expected); }
  } catch (error) { throw new Error(`${c.id}\n${c.source}\n${error.stack}`); }
}
if (process.argv.includes('--record-baseline')) {
  assert.ok(!process.argv.includes('--recover'));
  const source = readFileSync(new URL('../FHM/Unverified/Surface/Parse.lean', import.meta.url), 'utf8');
  writeFileSync(manifestPath, JSON.stringify({ version: 1, seed: '0x4f484d32', strictParserSha256: hash(source),
    cases: cases.map((c, i) => [c.id, hash(c.source), hash(results[i])]) }, null, 2) + '\n');
  console.log(`Recorded ${cases.length} pre-change strict parse fingerprints.`);
} else {
  const baseline = JSON.parse(readFileSync(manifestPath, 'utf8'));
  assert.equal(baseline.cases.length, cases.length);
  for (let i = 0; i < cases.length; i++) {
    const [id, sourceHash, resultHash] = baseline.cases[i];
    assert.equal(cases[i].id, id);
    assert.equal(hash(cases[i].source), sourceHash, `${id}: generator changed`);
    assert.equal(hash(results[i]), resultHash, `${id}: strict parse changed\n${cases[i].source}\n${JSON.stringify(results[i])}`);
  }
  console.log(`PASS ${cases.length} frozen strict parses (AST, spans, binders, exact failures).`);
}
console.log(`PASS ${cases.filter(c => c.expected).length} independently generated AST round trips.`);

if (!process.argv.includes('--record-baseline')) {
  const partials = run(cases.map(({ source, kind }) => ({ source, kind, mode: 'partial' })));
  let recovered = 0, islands = 0;
  function verify(c, strict, partial) {
    try {
      if (strict.ok) {
        assert.equal(partial.ok, true, 'valid input rejected by editor');
        assert.deepEqual(partial.holes, [], 'valid input gained errors');
        for (const key of ['ast', 'binders', 'spans']) assert.deepEqual(partial[key], strict[key], `valid ${key} changed`);
      }
      if (partial.ok) {
        assert.equal(partial.registryOk, true, 'orphan/duplicated error leaf');
        assert.equal(partial.holes.length === 0, !!strict.ok, 'invalid input silently repaired');
        if (partial.strictProjection !== undefined) assert.equal(partial.strictProjection, partial.holes.length === 0);
        for (const hole of partial.holes) assert.ok(hole.first <= hole.last, 'backward recovery range');
        for (const fragment of partial.fragments) {
          islands++;
          assert.equal(fragment.parsed.ok, true, `retained fragment does not parse from its original token interval: ${JSON.stringify(fragment)}`);
          assert.deepEqual(fragment.parsed.ast, fragment.ast, 'retained fragment AST differs from its original source');
        }
        if (partial.holes.length) recovered++;
      }
    } catch (error) { throw new Error(`${c.id}\n${c.source}\n${error.stack}`); }
  }
  cases.forEach((c, i) => verify(c, results[i], partials[i]));
  const extras = [];
  const operators = [['+', 'PrimBinOp.intAdd'], ['-', 'PrimBinOp.intSub'], ['<', 'PrimBinOp.intLt']];
  for (let i = 0; i < 360; i++) {
    const a = expr(3), b = expr(2), n = `capture${i}`;
    const [operator, tag] = operators[i % operators.length];
    extras.push({ id: `infix-${i}`, kind: 'expr', source: `(${a.source} ${operator} ${b.source})`,
      expected: ['app', ['app', ['op', tag], a.ast], b.ast] });
    extras.push({ id: `match-${i}`, kind: 'expr', source: `(match ${a.source} with | ${n} -> ${n})`,
      expected: ['match', a.ast, [[['name', n], ['var', n]]]] });
    extras.push({ id: `cons-${i}`, kind: 'expr', source: `(${a.source} :: ${b.source})`, expected: ['cons', a.ast, b.ast] });
    extras.push({ id: `lambdas-${i}`, kind: 'expr', source: `(\\x${i} y${i} -> (x${i}, y${i}))`, expected:
      ['lambda', ['name', `x${i}`], null, ['lambda', ['name', `y${i}`], null, ['pair', ['var', `x${i}`], ['var', `y${i}`]]]] });
  }
  const alphabet = ['(', ')', '[', ']', '{', '}', ',', '=', ':', '->', '\\', '+', '::', '|',
    'let', 'in', 'if', 'then', 'else', 'match', 'with', 'type', 'x', 'Int', 'True', '1', '/- ( let -/'];
  for (let i = 0; i < 800; i++) extras.push({ id: `tokens-${i}`, kind: i % 2 ? 'expr' : 'program',
    source: Array.from({ length: 1 + random(32) }, () => alphabet[random(alphabet.length)]).join(' ') });
  const strictExtras = run(extras), partialExtras = run(extras.map(c => ({ ...c, mode: 'partial' })));
  extras.forEach((c, i) => {
    if (c.expected) {
      assert.equal(strictExtras[i].ok, true, c.source);
      assert.deepEqual(strictExtras[i].ast, c.expected, c.source);
    }
    verify(c, strictExtras[i], partialExtras[i]);
  });
  console.log(`PASS ${extras.filter(c => c.expected).length} additional generated infix, cons, match and multiple-lambda ASTs.`);
  console.log(`PASS ${cases.length + extras.length} strict/editor conservation and recovery checks; ${recovered} recovered inputs, ${islands} independently reparsed islands.`);
}
