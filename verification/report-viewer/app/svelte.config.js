import { vitePreprocess } from "@sveltejs/vite-plugin-svelte";
// `lang="ts"` in a component goes through the same type stripping as the rest.
export default { preprocess: vitePreprocess() };
