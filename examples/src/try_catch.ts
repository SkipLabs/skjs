// Valid try/catch examples
function basicTryCatch(): void {
  try {
    throw new Error("test error");
  } catch (e) {
    console.log("Caught:", e);
  }
}

function tryCatchWithType(): void {
  try {
    throw "string error";
  } catch (e: string) {
    console.log("Caught string:", e);
  }
}

function tryFinally(): void {
  let x: number = 0;
  try {
    x = 1;
  } finally {
    x = 2;
  }
}

function tryCatchFinally(): void {
  try {
    throw new Error("test");
  } catch (e: Error) {
    console.log("caught:", e.message);
  } finally {
    console.log("finally executed");
  }
}

function nestedTryCatch(): void {
  try {
    try {
      throw new Error("inner error");
    } catch (inner: Error) {
      console.log("inner catch:", inner.message);
      throw new Error("outer error");
    }
  } catch (outer: Error) {
    console.log("outer catch:", outer.message);
  }
}

function asyncTryCatch(): void {
  try {
    // Just a simple async operation without Promise references
    console.log("async operation");
  } catch (e) {
    console.log("async error:", e);
  }
}

function tryWithReturn(): number {
  try {
    return 1;
  } catch (e) {
    return 2;
  }
}

function catchWithoutParam(): void {
  try {
    throw new Error("test");
  } catch {
    console.log("caught something");
  }
}

function multipleThrowTypes(): void {
  try {
    if (Math.random() > 0.5) {
      throw new Error("error object");
    } else {
      throw "string error";
    }
  } catch (e) {
    // e has type 'any' since multiple types can be thrown
    console.log("Caught:", e);
  }
}

function tryCatchInLoop(): void {
  for (let i: number = 0; i < 10; i++) {
    try {
      if (i === 5) {
        throw new Error("number is 5");
      }
      console.log("Processing:", i);
    } catch (e) {
      console.log("Error at iteration", i, ":", e);
      continue;
    }
  }
}
