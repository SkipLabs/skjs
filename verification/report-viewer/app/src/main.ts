import { mount } from "svelte";
import App from "./App.svelte";
import "./reader.css";

const target = document.getElementById("reader");
if (!target) throw new Error("the page has no mount point");
mount(App, { target });
