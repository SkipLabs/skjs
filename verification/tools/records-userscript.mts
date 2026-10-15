/* Builds a userscript (Tampermonkey, Violentmonkey) that shows a pull
 * request's commit records on GitHub, drawn as the review page draws them.
 * On a pull request's conversation tab it draws the records of the pull
 * request's commits in place of its description (a toggle shows the
 * description); on every pull request page a "Records" button shows them
 * over the page. The commits are read
 * from the pull request's `.patch`, in the reviewer's signed-in browser, so
 * private repositories work. The drawing is record-render.mts, compiled into
 * the script.
 *
 *   node verification/tools/records-userscript.mts --out records.user.js
 */
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { stripTypeScriptTypes } from "node:module";

const args = process.argv.slice(2);
const outAt = args.indexOf("--out");
if (outAt < 0 || outAt + 1 >= args.length) throw new Error("usage: records-userscript.mts --out <records.user.js>");
const outFile = args[outAt + 1];

// The renderer as plain browser JavaScript: types erased, `export` dropped,
// in the script's own scope.
const source = readFileSync(join(import.meta.dirname, "record-render.mts"), "utf8");
const compiled = stripTypeScriptTypes(source).replace(/^export (?=(const|function|let) )/gm, "");

const runtime = String.raw`
/** The commits of a pull request, from its mbox \`.patch\`: each one's hash,
 * author and date, full message and file summary. */
function parsePatch(mbox) {
  const commits = [];
  for (const chunk of mbox.split(/^From ([0-9a-f]{40}) /m).slice(1).reduce((acc, x, i, all) => (i % 2 ? acc : [...acc, [x, all[i + 1]]]), [])) {
    const [sha, text] = chunk;
    const blank = text.indexOf("\n\n");
    const headers = text.slice(0, blank).replace(/\n[ \t]+/g, " ");
    const header = name => (new RegExp("^" + name + ": (.*)$", "m").exec(headers) || [])[1] || "";
    const subject = header("Subject").replace(/^\[PATCH[^\]]*\]\s*/, "");
    const rest = text.slice(blank + 2);
    const cut = rest.search(/^---$/m);
    const body = (cut >= 0 ? rest.slice(0, cut) : rest).replace(/\n+$/, "");
    const statEnd = cut >= 0 ? rest.indexOf("\n\n", cut) : -1;
    const stat = cut >= 0 ? rest.slice(cut + 4, statEnd >= 0 ? statEnd : undefined).split("\n").filter(l => /\||changed/.test(l)) : [];
    const date = new Date(header("Date"));
    const when = isNaN(date) ? "" : " · " + date.toLocaleString("en-US", { month: "short", day: "2-digit", hour: "2-digit", minute: "2-digit", hour12: false });
    const author = header("From").replace(/\s*<[^>]*>/, "").replace(/^"|"$/g, "");
    const message = subject + (body ? "\n\n" + body : "") + "\n";
    commits.push(parseRecord(message, { sha: sha.slice(0, 9), author: author + when, stat, message }));
  }
  return commits;
}

function fetchText(url) {
  return new Promise((resolve, reject) => GM.xmlHttpRequest({
    method: "GET", url,
    onload: r => (r.status === 200 ? resolve(r.responseText) : reject(new Error(url + ": " + r.status))),
    onerror: () => reject(new Error(url + ": network error")),
  }));
}

/** The commits through GitHub's API, with a personal access token (read
 * access to the repository's contents and pull requests), asked for once
 * and kept in the extension's storage: each commit's message, author, date
 * and changed files. */
async function apiRecords(owner, repo, number) {
  let token = await GM.getValue("token", "");
  if (!token) {
    token = (prompt("Commit records: a GitHub token that can read " + owner + "/" + repo + " (kept in this extension's storage)") || "").trim();
    if (!token) throw new Error("no token given");
    await GM.setValue("token", token);
  }
  const api = async path => {
    const r = await fetch("https://api.github.com/repos/" + owner + "/" + repo + path, { headers: { Authorization: "Bearer " + token, Accept: "application/vnd.github+json" } });
    if (r.status === 401) await GM.setValue("token", "");
    if (!r.ok) throw new Error("GitHub API " + path + ": " + r.status);
    return r.json();
  };
  const commits = await api("/pulls/" + number + "/commits?per_page=100");
  return Promise.all(commits.map(async c => {
    const full = await api("/commits/" + c.sha);
    const files = full.files || [];
    const width = Math.max(0, ...files.map(f => f.filename.length));
    const stat = files.map(f => " " + f.filename.padEnd(width) + " | " + String(f.changes).padStart(4) + " " + "+".repeat(Math.min(f.additions, 40)) + "-".repeat(Math.min(f.deletions, 40)));
    const add = files.reduce((n, f) => n + f.additions, 0), del = files.reduce((n, f) => n + f.deletions, 0);
    stat.push(" " + files.length + " file" + (files.length === 1 ? "" : "s") + " changed, " + add + " insertion" + (add === 1 ? "" : "s") + "(+), " + del + " deletion" + (del === 1 ? "" : "s") + "(-)");
    const date = new Date(c.commit.author.date);
    const author = c.commit.author.name + " · " + date.toLocaleString("en-US", { month: "short", day: "2-digit", hour: "2-digit", minute: "2-digit", hour12: false });
    return parseRecord(c.commit.message, { sha: c.sha.slice(0, 9), author, stat, message: c.commit.message });
  }));
}

/** The records of a pull request's commits: its \`.patch\` read with the
 * reviewer's GitHub session (from the page, then through the extension),
 * else GitHub's API with a token. */
async function readRecords(owner, repo, number) {
  const url = "https://github.com/" + owner + "/" + repo + "/pull/" + number + ".patch";
  const tried = [];
  try {
    const r = await fetch(url, { credentials: "include" });
    if (r.ok) return parsePatch(await r.text());
    tried.push("page: " + r.status);
  } catch (e) { tried.push("page: " + e); }
  try { return parsePatch(await fetchText(url)); } catch (e) { tried.push("extension: " + e.message); }
  try { return await apiRecords(owner, repo, number); } catch (e) { tried.push("API: " + e.message); }
  throw new Error(tried.join("; "));
}

// The records of each pull request this page has shown, read once.
const cache = new Map();
function recordsFor(owner, repo, number) {
  const key = owner + "/" + repo + "#" + number;
  if (!cache.has(key)) cache.set(key, readRecords(owner, repo, number).catch(e => { cache.delete(key); throw e; }));
  return cache.get(key);
}

// The page's styles, scoped to a shadow root: its document rules apply to
// the root's page element, its theme follows GitHub's.
const scopedCss = CSS.replace(/:root\[data-theme="dark"\]/g, ":host([data-theme=dark])").replace(/:root:not\(\[data-theme="light"\]\)/g, ":host(:not([data-theme=light]))").replace(/:root/g, ":host").replace(/\bbody \{/g, ".page {");
function theme() {
  const mode = document.documentElement.getAttribute("data-color-mode");
  if (mode === "dark" || mode === "light") return mode;
  return matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
}

let host;
function close() { if (host) { host.remove(); host = undefined; } }

async function open(owner, repo, number) {
  close();
  host = document.createElement("div");
  host.style.cssText = "position:fixed;inset:0;z-index:2147483646;overflow:auto";
  host.setAttribute("data-theme", theme());
  const root = host.attachShadow({ mode: "open" });
  root.innerHTML = "<style>" + scopedCss + " .page{min-height:100%} .close{position:fixed;top:12px;right:16px;font:600 13px/1 var(--body);padding:8px 12px;border-radius:6px;border:1px solid var(--rule);background:var(--surface);color:var(--ink);cursor:pointer}</style><div class=page><main><p class=lede>Reading the commits of #" + number + "…</p></main></div><button class=close>Close (Esc)</button>";
  root.querySelector(".close").addEventListener("click", close);
  document.body.appendChild(host);
  try {
    const records = await recordsFor(owner, repo, number);
    root.querySelector(".page").innerHTML = pageBody([{ name: "pr-" + number, range: owner + "/" + repo + "#" + number, records, files: [] }]);
  } catch (e) {
    root.querySelector(".page").innerHTML = "<main><p class=lede>Could not read the commits: " + esc(String(e)) + "</p></main>";
  }
}

document.addEventListener("keydown", e => { if (e.key === "Escape") close(); });

/** The records in place of the pull request's description, on its
 * conversation tab: the description is the comment GitHub gives the id
 * "pullrequest-…". A toggle shows the description again. Nothing happens
 * where the page has no such comment; the button still works. */
function drawInPlace(owner, repo, number) {
  const body = document.querySelector('[id^="pullrequest-"] .js-comment-body');
  if (!body || body.previousElementSibling?.id === "commit-records-inline") return;
  const box = document.createElement("div");
  box.id = "commit-records-inline";
  box.setAttribute("data-theme", theme());
  const root = box.attachShadow({ mode: "open" });
  root.innerHTML = "<style>" + scopedCss + " :host{display:block;padding:8px 16px} .page{background:transparent} main{padding:8px 0;max-width:none;gap:16px} .bar{display:flex;gap:8px;align-items:center;font:12px/1 var(--body);color:var(--muted)} .bar button{font:600 12px/1 var(--body);padding:6px 10px;border-radius:6px;border:1px solid var(--rule);background:var(--surface);color:var(--ink);cursor:pointer}</style>" +
    "<div class=page><main><div class=bar><span>Commit records of #" + number + ", drawn from the commits</span><button class=toggle>Show description</button></div><div class=records><p class=lede>Reading the commits…</p></div></main></div>";
  body.before(box);
  // GitHub's own classes force the description visible with !important.
  const showDescription = shown => {
    if (shown) body.style.removeProperty("display"); else body.style.setProperty("display", "none", "important");
    root.querySelector(".records").style.display = shown ? "none" : "";
    root.querySelector(".toggle").textContent = shown ? "Show records" : "Show description";
  };
  let described = false;
  showDescription(described);
  root.querySelector(".toggle").addEventListener("click", () => showDescription(described = !described));
  recordsFor(owner, repo, number).then(records => {
    const group = { name: "pr-" + number, range: owner + "/" + repo + "#" + number, records, files: [] };
    root.querySelector(".records").innerHTML = summary([group]) + records.map(card).join("\n");
  }).catch(e => {
    root.querySelector(".records").innerHTML = "<p class=lede>Could not read the commits: " + esc(String(e)) + "</p>";
    body.style.removeProperty("display");
  });
}

// GitHub navigates without reloading, and redraws the timeline: keep the
// button and the drawing in step with the page.
function sync() {
  const m = /^\/([^/]+)\/([^/]+)\/pull\/(\d+)/.exec(location.pathname);
  let button = document.getElementById("commit-records-button");
  if (!m) { if (button) button.remove(); close(); return; }
  if (!button) {
    button = document.createElement("button");
    button.id = "commit-records-button";
    button.textContent = "Records";
    button.style.cssText = "position:fixed;bottom:20px;right:20px;z-index:2147483645;font:600 13px/1 -apple-system,BlinkMacSystemFont,sans-serif;padding:10px 14px;border-radius:20px;border:1px solid #1f6f66;background:#1f6f66;color:#fff;cursor:pointer;box-shadow:0 2px 8px rgba(0,0,0,.2)";
    document.body.appendChild(button);
  }
  button.onclick = () => open(m[1], m[2], m[3]);
  drawInPlace(m[1], m[2], m[3]);
}
sync();
setInterval(sync, 1000);
`;

const header = `// ==UserScript==
// @name         Commit records on GitHub
// @description  Shows a pull request's commit records as the review page draws them (built from verification/tools/record-render.mts).
// @namespace    skjs-verification
// @version      4
// @match        https://github.com/*
// @grant        GM.xmlHttpRequest
// @grant        GM.getValue
// @grant        GM.setValue
// @connect      github.com
// @connect      patch-diff.githubusercontent.com
// @connect      api.github.com
// ==/UserScript==
`;
writeFileSync(outFile, `${header}(() => {\n"use strict";\n${compiled}\n${runtime}\n})();\n`);
console.log(outFile);
