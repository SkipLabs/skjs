import { svelte } from "@sveltejs/vite-plugin-svelte";
import type { UserConfig } from "vite";

// The page is served by serve.js from `dist/`, so the build emits plain files
// with stable names rather than hashed ones: the server's asset table names
// them, and a hash would make that table a moving target.
export default {
  // The page is served from `/next`, and its assets from the server root, so
  // references are absolute from `/`.
  base: "/",
  plugins: [svelte()],
  build: {
    outDir: "dist",
    emptyOutDir: true,
    rollupOptions: {
      output: {
        entryFileNames: "reader.js",
        assetFileNames: "reader[extname]",
      },
    },
  },
} satisfies UserConfig;
