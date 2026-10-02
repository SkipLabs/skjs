import { svelte } from "@sveltejs/vite-plugin-svelte";
import type { UserConfig } from "vite";

// The page is served by serve.mts from `dist/`, so the build emits plain files
// with stable names rather than hashed ones: the server's asset table names
// them, and a hash would make that table a moving target.
export default {
  // The page and its assets are served from the server root, so
  // references are absolute from `/`.
  base: "/",
  plugins: [svelte()],
  build: {
    outDir: "dist",
    emptyOutDir: true,
    rollupOptions: {
      output: {
        entryFileNames: "viewer.js",
        assetFileNames: "viewer[extname]",
      },
    },
  },
} satisfies UserConfig;
