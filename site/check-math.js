#!/usr/bin/env node
// Checks that every formula in the generated site is valid KaTeX.
//
// Verso renders math in the browser with `throwOnError: false`, so a typo shows up as red text
// on the page rather than as a build error. This script renders every formula with the KaTeX
// bundled into the output (and the site's macros, read from the inline script in index.html)
// and fails if any formula does not parse.
//
// Usage: node check-math.js [_out/html-multi]
"use strict";
const fs = require("fs");
const path = require("path");

const root = process.argv[2] || path.join(__dirname, "_out", "html-multi");
const katex = require(path.resolve(root, "-verso-data", "katex", "katex.js"));

function* htmlFiles(dir) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, entry.name);
    if (entry.isDirectory()) yield* htmlFiles(p);
    else if (entry.name.endsWith(".html")) yield p;
  }
}

function unescapeHtml(s) {
  return s
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'")
    .replace(/&#x27;/g, "'")
    .replace(/&amp;/g, "&");
}

// The macro table is the JSON object passed to `Object.entries` in the inline script that
// `MilnorAlgDepSite.Support.Config` adds to every page.
const index = fs.readFileSync(path.join(root, "index.html"), "utf8");
const m = index.match(/Object\.entries\((\{.*?\})\)\) k\.__defineMacro/);
if (!m) {
  console.error("check-math: macro table not found in index.html");
  process.exit(1);
}
const macros = JSON.parse(m[1]);
for (const [name, body] of Object.entries(macros)) katex.__defineMacro(name, body);

let count = 0;
let failures = 0;
const re = /<code class="math (inline|display)">([\s\S]*?)<\/code>/g;
for (const file of htmlFiles(root)) {
  const html = fs.readFileSync(file, "utf8");
  for (const [, mode, raw] of html.matchAll(re)) {
    const tex = unescapeHtml(raw);
    count++;
    try {
      katex.renderToString(tex, { throwOnError: true, displayMode: mode === "display" });
    } catch (e) {
      failures++;
      console.error(`${path.relative(root, file)}: ${e.message}\n    ${tex}`);
    }
  }
}
console.log(`check-math: ${count} formulas, ${failures} errors`);
process.exit(failures === 0 ? 0 : 1);
