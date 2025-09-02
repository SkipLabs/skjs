// Test type errors in try/catch blocks
function validTryCatch(): void {
  try {
    throw new Error("test");
  } catch (e) {
    console.log(e);
  }
}

function invalidReturnInFinally(): number {
  try {
    return 1;
  } finally {
    // @ts-expect-error Invalid return type
    return "invalid";
  }
}
