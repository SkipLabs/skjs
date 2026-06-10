// Test unary operators with literal types (as const is automatic for const)

// Valid uses - const declarations with explicit literal type annotations
const negNumber: -42 = -42;
const negBigInt: -100n = -100n;
const plusNumber: 42 = +42;

// Object properties with as const where it's needed for non-kind fields
// @skjs-expect-error The type of a top-level constant must be a primitive type, not an object
const config: {
  port: -8080;
  timeout: 3000;
  offset: -100n;
} = {
  // @skjs-expect-error This 'as const' is unnecessary
  port: -8080 as const,
  // @skjs-expect-error This 'as const' is unnecessary
  timeout: +3000 as const,
  // @skjs-expect-error This 'as const' is unnecessary
  offset: -100n as const,
};

// Type inference from object properties
// type PortType = typeof config.port;
// type TimeoutType = typeof config.timeout;
