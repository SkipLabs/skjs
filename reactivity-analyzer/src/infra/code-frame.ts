/**
 * Small code-frame formatter for analyzer violations.
 *
 * Avoids extra dependencies (chalk, etc.) and keeps output stable.
 */

import fs from "node:fs";
import ts from "typescript";

export type CodeFrameOptions = {
  filePath: string;
  line: number; // 1-based
  col: number; // 1-based
  contextLinesBefore?: number;
  contextLinesAfter?: number;
  maxLineWidth?: number;
  highlightLength?: number;
};

function useColor(): boolean {
  if (process.env.NO_COLOR !== undefined) return false;
  if (process.env.FORCE_COLOR !== undefined) return true;
  if (process.env.SKCHECK_FORCE_COLOR !== undefined) return true;
  if (!process.stderr.isTTY) return false;
  return true;
}

function c(code: number, s: string): string {
  if (!useColor()) return s;
  return `\u001b[${code}m${s}\u001b[0m`;
}

function dim(s: string): string {
  return c(90, s);
}

function red(s: string): string {
  return c(31, s);
}

function boldRed(s: string): string {
  if (!useColor()) return s;
  return `\u001b[1;31m${s}\u001b[0m`;
}

function clamp(n: number, min: number, max: number): number {
  return Math.max(min, Math.min(max, n));
}

function truncateLine(
  text: string,
  caretCol0: number,
  maxWidth: number,
): { text: string; caretCol0: number } {
  if (text.length <= maxWidth) return { text, caretCol0 };
  const ell = "…";
  const inner = Math.max(1, maxWidth - 2 * ell.length);
  const start = clamp(
    caretCol0 - Math.floor(inner / 2),
    0,
    Math.max(0, text.length - inner),
  );
  const end = Math.min(text.length, start + inner);
  const sliced = text.slice(start, end);
  const prefix = start > 0 ? ell : "";
  const suffix = end < text.length ? ell : "";
  const newCaret = caretCol0 - start + prefix.length;
  return { text: `${prefix}${sliced}${suffix}`, caretCol0: newCaret };
}

function makeCaretPadding(linePrefix: string): string {
  // Preserve tabs in prefix so caret alignment matches terminal rendering.
  return linePrefix.replace(/[^\t]/g, " ");
}

function isKeyword(tok: ts.SyntaxKind): boolean {
  return tok >= ts.SyntaxKind.FirstKeyword && tok <= ts.SyntaxKind.LastKeyword;
}

function highlightTsLine(text: string): string {
  if (!useColor()) return text;
  if (text.length === 0) return text;

  const scanner = ts.createScanner(
    ts.ScriptTarget.Latest,
    /* skipTrivia */ false,
    ts.LanguageVariant.Standard,
    text,
  );

  let out = "";
  let pos = 0;
  for (;;) {
    const token = scanner.scan();
    if (token === ts.SyntaxKind.EndOfFileToken) break;

    const tokenPos = scanner.getTokenPos();
    const textPos = scanner.getTextPos();
    if (tokenPos > pos) out += text.slice(pos, tokenPos);

    const tokenText = text.slice(tokenPos, textPos);

    let colored = tokenText;
    if (token === ts.SyntaxKind.SingleLineCommentTrivia || token === ts.SyntaxKind.MultiLineCommentTrivia) {
      colored = dim(tokenText);
    } else if (
      token === ts.SyntaxKind.StringLiteral ||
      token === ts.SyntaxKind.NoSubstitutionTemplateLiteral ||
      token === ts.SyntaxKind.TemplateHead ||
      token === ts.SyntaxKind.TemplateMiddle ||
      token === ts.SyntaxKind.TemplateTail ||
      token === ts.SyntaxKind.RegularExpressionLiteral
    ) {
      colored = c(32, tokenText);
    } else if (token === ts.SyntaxKind.NumericLiteral || token === ts.SyntaxKind.BigIntLiteral) {
      colored = c(35, tokenText);
    } else if (isKeyword(token)) {
      colored = c(36, tokenText);
    }

    out += colored;
    pos = textPos;
  }

  if (pos < text.length) out += text.slice(pos);
  return out;
}

export function formatCodeFrame(opts: CodeFrameOptions): string | null {
  const contextLinesBefore = opts.contextLinesBefore ?? 4;
  const contextLinesAfter = opts.contextLinesAfter ?? 2;
  const maxLineWidth = opts.maxLineWidth ?? 140;
  const highlightLength = Math.max(1, opts.highlightLength ?? 1);

  let content: string;
  try {
    content = fs.readFileSync(opts.filePath, "utf8");
  } catch {
    return null;
  }

  const rawLines = content.split(/\r?\n/);
  if (rawLines.length === 0) return null;

  const targetLine1 = clamp(opts.line, 1, rawLines.length);
  const startLine1 = clamp(targetLine1 - contextLinesBefore, 1, rawLines.length);
  const endLine1 = clamp(targetLine1 + contextLinesAfter, 1, rawLines.length);
  const lineNoWidth = String(endLine1).length;

  const parts: string[] = [];

  for (let line1 = startLine1; line1 <= endLine1; line1++) {
    const raw = rawLines[line1 - 1] ?? "";

    const prefix = String(line1).padStart(lineNoWidth, " ");
    const isTarget = line1 === targetLine1;
    const gutter = isTarget ? boldRed(">") : " ";
    const bar = dim("|");

    const caretInRaw0 = isTarget ? clamp(opts.col - 1, 0, Math.max(0, raw.length)) : 0;
    const shown = truncateLine(raw, caretInRaw0, maxLineWidth);
    const displayText = shown.text;
    const caretCol0 = shown.caretCol0;
    const displayTextColored = highlightTsLine(displayText);

    parts.push(
      `${gutter} ${prefix} ${bar} ${displayTextColored}`,
    );

    if (isTarget) {
      const pad = makeCaretPadding(displayText.slice(0, caretCol0));
      const marker = "^".repeat(highlightLength);
      parts.push(`${dim(" ")} ${" ".repeat(lineNoWidth)} ${bar} ${pad}${red(marker)}`);
    }
  }

  return parts.join("\n");
}
