// Mounts App.svelte, the reader, on the page and loads reader.css, its palette,
// for the bundler to emit; assets.d.ts declares that stylesheet import's module.
import { mount } from "svelte";
import App from "./App.svelte";
import "./reader.css";

const target = document.getElementById("reader");
if (!target) throw new Error("the page has no mount point");
mount(App, { target });
