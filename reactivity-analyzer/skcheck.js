#!/usr/bin/env node
/**
 * skcheck - thin wrapper that auto-builds if needed
 */

import { existsSync } from "node:fs";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { dirname, join } from "node:path";

const __dirname = dirname(fileURLToPath(import.meta.url));
const distCli = join(__dirname, "dist", "cli.js");

async function run(cmd, args, cwd) {
  return new Promise((resolve, reject) => {
    const proc = spawn(cmd, args, { cwd, stdio: "inherit" });
    proc.on("close", (code) => (code === 0 ? resolve() : reject(new Error(`Exit ${code}`))));
    proc.on("error", reject);
  });
}

async function build() {
  console.log("Building skcheck...");
  await run("npm", ["install"], __dirname);
  await run("npm", ["run", "build"], __dirname);
  console.log("Build complete.\n");
}

async function main() {
  const args = process.argv.slice(2);

  // Explicit build command
  if (args[0] === "build") {
    await build();
    return;
  }

  // Auto-build if dist doesn't exist
  if (!existsSync(distCli)) {
    await build();
  }

  // Run the real CLI
  const cli = await import(distCli);
  // cli.main() is called automatically on import
}

main().catch((err) => {
  console.error(err.message);
  process.exit(1);
});
