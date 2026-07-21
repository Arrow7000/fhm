import { defineConfig } from "vite";
import path from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

// Browser: Vite prebundles fhmEditorCore.cjs with needsInterop (named exports).
// VS Code / hover-sweep: require("../shared/fhmEditorCore.cjs") directly.
const editorCoreCjs = path.resolve(__dirname, "../shared/fhmEditorCore.cjs");

export default defineConfig({
  root: ".",
  publicDir: "public",
  resolve: {
    alias: {
      "@fhm/editor-core": editorCoreCjs,
    },
  },
  server: {
    // Express mounts Vite in middleware mode (`npm run dev` → server.mjs).
    middlewareMode: true,
  },
  build: {
    outDir: "dist",
    emptyOutDir: true,
  },
  optimizeDeps: {
    // Prebundle CJS core so the browser gets ESM named exports (not raw @fs .cjs).
    // After editing editors/shared/fhmEditorCore.cjs, run `npm run dev:clean`.
    include: ["@fhm/editor-core", "monaco-editor", "vscode-oniguruma", "vscode-textmate"],
    needsInterop: ["@fhm/editor-core", "vscode-oniguruma", "vscode-textmate"],
  },
});
