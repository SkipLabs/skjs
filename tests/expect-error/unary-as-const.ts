// Test unary operators with literal types (as const is automatic for const)

// Valid uses - const declarations with explicit literal type annotations
const negNumber: -42 = -42;
const negBigInt: -100n = -100n;
const plusNumber: 42 = +42;

// Object properties with as const where it's needed for non-kind fields
// @skjs-expect-error Invalid type for constant, only primitive types (not objects) are allowed
const config: {
  port: -8080;
  timeout: 3000;
  offset: -100n;
} = {
  port: -8080 as const,
  timeout: +3000 as const,
  offset: -100n as const,
};

// Type inference from object properties
type PortType = typeof config.port;
type TimeoutType = typeof config.timeout;
