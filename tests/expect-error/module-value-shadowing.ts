// Collides with the builtin `process` value (TS2300, issue #887).
// @skjs-expect-error Duplicate identifier 'process'
function process(n: number): number {
  return n + 1;
}

export function callLocal(): number {
  return process(41);
}

export function readMissingProperty(): string | undefined {
  // @ts-expect-error Property 'env' does not exist on this type
  return process.env["HOME"];
}

type console = { value: number };

export function callAmbient(): void {
  console.log("ambient");
}

export function checkShadowedArray(value: unknown): number {
  const Array = { isArray: (candidate: unknown): boolean => true };
  if (Array.isArray(value)) {
    // @ts-expect-error Cannot access a property on type 'unknown'
    return value.length;
  }
  return 0;
}
