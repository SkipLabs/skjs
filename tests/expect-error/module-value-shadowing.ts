function process(n: number): number {
  return n + 1;
}

export function callLocal(): number {
  // @skjs-expect-error This expression is not callable
  return process(41);
}

export function readMissingProperty(): string | undefined {
  return process.env["HOME"];
}

type console = { value: number };

export function callAmbient(): void {
  console.log("ambient");
}
