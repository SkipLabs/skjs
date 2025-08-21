// Test template literals with different types
const name: string = "Alice";
const age: number = 30;
const isActive: boolean = true;
const nullValue: null = null;
const undefinedValue: undefined = undefined;

// Simple template without interpolation
const simple: string = `Hello World`;

// Template with string interpolation
const withString: string = `Hello ${name}`;

// Template with number interpolation
const withNumber: string = `Age: ${age}`;

// Template with boolean interpolation
const withBoolean: string = `Active: ${isActive}`;

// Template with null interpolation
const withNull: string = `Value: ${nullValue}`;

// Template with undefined interpolation
const withUndefined: string = `Value: ${undefinedValue}`;

// Complex template with multiple types
const complex: string = `User ${name} (${age}) is ${isActive ? "active" : "inactive"}`;

// Multiline template literal
const multiline: string = `Line 1: ${name}
Line 2: ${age}
Line 3: ${isActive}`;