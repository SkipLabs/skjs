// Template literal parsing tests for SKJS
// These test that template literals parse correctly without syntax errors
// Including corner cases, nested constructs, and aggressive edge cases

export function main(): void {
  // Basic cases
  const simple = `hello world`;
  const empty = ``;
  const onlyExpr = `${42}`;
  
  // Multiple interpolations
  const multiple = `${1} ${2} ${3} ${4} ${5}`;
  
  // Back-to-back interpolations with no text between
  const backToBack = `${1}${2}${3}`;
  
  // Starting and ending with interpolations
  const startEnd = `${1} middle ${2}`;
  
  // Complex expressions
  const complex = `${1 + 2 * 3 - 4 / 5}`;
  const withParens = `${(1 + 2) * (3 + 4)}`;
  const ternary = `${true ? "yes" : "no"}`;
  
  // Nested function calls and method chains
  const nested = `${Math.max(1, 2, 3)}`;
  const chained = `${[1, 2, 3].map(x => x * 2).join(", ")}`;
  
  // Object and array access
  const obj = { a: { b: { c: 42 } } };
  const arr = [[1, 2], [3, 4]];
  const deepAccess = `${obj.a.b.c}`;
  const arrayAccess = `${arr[0][1]}`;
  
  // Template literals inside expressions
  const innerTemplate = `outer ${`inner ${42} text`} outer`;
  const doubleNested = `a ${`b ${`c`} b`} a`;
  const tripleNested = `1 ${`2 ${`3 ${4} 3`} 2`} 1`;
  
  // Template literals with function calls containing templates
  const funcWithTemplate = `${someFunc(`param ${value} param`)}`;
  const complexNest = `${process(`${data.map(x => `item ${x}`).join(" ")}`)}`;
  
  // Escaped backticks and dollar signs
  const escapedTick = `text \` text`;
  const escapedDollar = `text \$ text`;
  const escapedBrace = `text \${ text`;
  const escapedInterpolation = `text \${expr} text`;
  
  // Special characters and unicode
  const special = `\n\t\r"'\\`;
  const unicode = `\u0041\u0042\u0043`;
  const emoji = `Hello 👋 World 🌍`;
  
  // Very long templates
  const longText = `This is a very long template literal that spans multiple conceptual lines and contains ${1} interpolation ${2} and more ${3} text that keeps going and going`;
  
  // Many interpolations
  const manyInterps = `${1}${2}${3}${4}${5}${6}${7}${8}${9}${10}`;
  
  // Multiline with interpolations
  const multilineComplex = `Line 1: ${1}
Line 2: ${2}
Line 3: ${3}`;
  
  // Interpolations with complex object destructuring
  const { prop1, prop2 } = obj;
  const destructured = `${prop1} and ${prop2}`;
  
  // Templates in array/object literals
  const arrayWithTemplates = [`${1}`, `${2}`, `${3}`];
  const objWithTemplates = {
    key1: `value ${1}`,
    key2: `value ${2}`,
    [`key${3}`]: `value ${3}`
  };
  
  // Templates as function arguments
  someFunction(`arg1 ${value}`, `arg2 ${other}`, `arg3 ${more}`);
  
  // Templates in conditionals and loops
  if (`condition ${check}` === "something") {
    const inIf = `inside if ${value}`;
  }
  
  for (const item of items) {
    const inLoop = `item: ${item}`;
  }
  
  // Templates with typeof, instanceof
  const withTypeof = `type is ${typeof value}`;
  const withInstanceof = `is array: ${arr instanceof Array}`;
  
  // Templates with async/await (if supported)
  const withAwait = `result: ${await someAsyncFunc()}`;
  
  // Extreme nesting stress test
  const extremeNest = `a${`b${`c${`d${`e${`f${`g${42}g`}f`}e`}d`}c`}b`}a`;
  
  // Templates with all operators
  const allOps = `${a + b} ${a - b} ${a * b} ${a / b} ${a % b} ${a ** b}`;
  const bitwise = `${a & b} ${a | b} ${a ^ b} ${~a} ${a << 1} ${a >> 1}`;
  const logical = `${a && b} ${a || b} ${!a}`;
  const comparison = `${a === b} ${a !== b} ${a < b} ${a > b} ${a <= b} ${a >= b}`;
  
  // Templates with try/catch
  try {
    const inTry = `trying ${operation}`;
  } catch (e) {
    const inCatch = `error: ${e.message}`;
  }
  
  // Edge case: template as template tag
  const tagged = tag`template ${value} literal`;
  
  // Empty interpolations and whitespace edge cases
  const emptyInterp = `${}`;
  const whitespaceInterp = `${ }`;
  const tabInterp = `${	42	}`;
  
  function someFunc(param: string): string { return param; }
  function process(data: string): string { return data; }
  function someFunction(...args: string[]): void {}
  async function someAsyncFunc(): Promise<string> { return "async"; }
  function tag(strings: TemplateStringsArray, ...values: any[]): string { return ""; }
}