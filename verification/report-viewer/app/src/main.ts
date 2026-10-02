// Mounts App.svelte, the report viewer, on the page and loads viewer.css, its palette,
// for the bundler to emit; assets.d.ts declares that stylesheet import's module.
import { mount } from "svelte";
import App from "./App.svelte";
import "./viewer.css";

const target = document.getElementById("viewer");
if (!target) throw new Error("the page has no mount point");
mount(App, { target });
