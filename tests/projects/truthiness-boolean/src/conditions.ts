// truthiness mode "boolean" (strict): a condition must be a subtype of boolean.
// Everything else is rejected. tsc accepts these truthiness tests, so the
// rejections are SKJS-specific.

// --- Accepted: boolean (and its subtypes) + narrowing ----------------------

function acceptBoolean(b: boolean): void {
  if (b) {
    const t: true = b;
  } else {
    const f: false = b;
  }
}

function acceptWhileTrue(): void {
  while (true) {
    break;
  }
}

function acceptIfFalse(): void {
  if (false) {
  }
}

// --- Rejected: not a subtype of boolean ------------------------------------

function rejectObjUndefined(o: { a: number } | undefined): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (o) {
  }
}

function rejectString(s: string): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (s) {
  }
}

function rejectNumber(n: number): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (n) {
  }
}

// `unknown` (the top type) is not a subtype of boolean; tsc accepts it, so this
// is SKJS-only.
function rejectUnknown(x: unknown): void {
  // @skjs-expect-error A condition must be of type 'boolean'
  if (x) {
  }
}
