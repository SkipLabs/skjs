# SKJS TypeScript Subset Rules

This document describes the rules and restrictions of the SKJS type checker, which implements a sound subset of TypeScript.

## Key Restrictions Discovered

### 1. No Toplevel `let` Declarations
- **Rule**: Cannot use `let` at the top level of files
- **Error**: "Construction not supported: toplevel let"
- **Workaround**: Use function declarations or class methods instead

### 2. Array Literals vs Tuples
- **Rule**: `[]` syntax creates tuples, not `Array<T>` types
- **Array Usage**: Use `new Array<T>()` for homogeneous collections
- **Tuple Usage**: Use `[value1, value2]` for heterogeneous fixed-length collections
- **Example**: `let arr: Array<number> = new Array<number>()` vs `let tuple = [1, "hello"]`

### 3. Class Inheritance Constructor Signatures
- **Rule**: Child class constructors must have same signature as parent
- **Error**: "Invalid extends" when constructor signatures differ
- **Requirement**: `constructor(a: T, b: U)` in parent requires same in child
- **Workaround**: Design inheritance hierarchies with consistent constructor patterns

### 4. Private Field Modifiers
- **Rule**: Private field modifiers are not fully implemented
- **Error**: "TODO: field modifier"
- **Workaround**: Avoid using private fields for now

#### 4b. Abstract Classes Not Supported
- **Rule**: Abstract classes and abstract method modifiers are not implemented  
- **Error**: "TODO: support for method modifiers (encountered abstract)"
- **Workaround**: Use regular classes with interfaces, or avoid abstract patterns

### 5. Console.log Argument Limitations
- **Rule**: console.log appears to have strict argument count limits
- **Error**: "Too many arguments" when passing multiple arguments
- **Workaround**: Use single arguments or string concatenation

### 6. Undefined Method Access
- **Rule**: Cannot call methods on potentially undefined values
- **Error**: "Invalid '.'" when accessing methods on `T | undefined`
- **Workaround**: Explicit undefined checks required

### 7. Generic Classes Work Properly ✅
- **Rule**: Generic classes with type parameters work correctly
- **Status**: Fixed - `new Array<T>()` assignment works in generic class constructors
- **Example**: `class Stack<T> { items: Array<T>; constructor() { this.items = new Array<T>(); } }`

### 8. Keyof Operator Not Implemented
- **Rule**: The `keyof` operator is not supported
- **Error**: "Invariant violation: TODO keyof"
- **Workaround**: Use explicit property access or type-specific functions

### 9. String Literals vs String Types
- **Rule**: Single quotes `'text'` create literal types, double quotes `"text"` create string types
- **Usage**: Use single quotes for union type members, double quotes for general strings
- **Example**: `type Status = 'active' | 'inactive'` but `let message: string = "Hello"`

### 10. Function Overloading Not Supported
- **Rule**: Function overloading is not supported in SKJS
- **Workaround**: Use different function names or union types with type guards

### 11. Generic Type Method Calls
- **Rule**: Cannot call methods like `.toString()` on unconstrained generic types
- **Error**: "Invalid '.' for type: T extends"
- **Workaround**: Use type constraints or avoid calling methods on raw generic types

### 12. Nested Function Declarations Not Supported
- **Rule**: Cannot declare functions inside other functions
- **Error**: "Function inside expressions are not supported, use closures instead"
- **Workaround**: Declare all functions at module level

### 13. Algebraic Data Types with 'kind' Field ✅
- **Rule**: ADTs must use `kind` field for discriminated unions
- **Syntax**: `type Foo = { kind: 'variant1', ... } | { kind: 'variant2', ... }`
- **Pattern Matching**: Use `if (value.kind === 'variant1')` for type narrowing
- **Special**: Only `kind` field enables ADT pattern matching, other field names won't work

### 14. Import System ✅
- **Rule**: Imports must use relative paths starting with `./` and ending with `.js`
- **Syntax**: `import { functionName, TypeName } from './filename.js'`
- **Requirements**: File must start with `./` and end with `.js` extension
- **Example**: `import { add, User } from './utils.js'`

### 15. Only Locals Can Be Compared to null/undefined
- **Rule**: Only local variables can be directly compared to `null`, `undefined`, or string literals
- **Limitation**: Cannot compare property access expressions like `x.foo` or `obj.property` to null/undefined
- **Error**: Expressions like `if (x.foo != null)` or `while (current.next !== null)` will fail
- **Workaround**: Assign property to local variable first, then perform comparison
- **Example**: 
  ```typescript
  // Won't work - comparing property access to null
  if (x.foo != null) {
    x.foo.someMethod(); // Error: "Only locals can be compared to null/undefined"
  }
  
  // Works - compare local variable to null
  let foo = x.foo;
  if (foo != null) {
    foo.someMethod(); // Success: local comparison works
  }
  
  // Won't work - comparing property in loop
  while (current.next !== null) { // Error
    current = current.next;
  }
  
  // Works - use local variable in loop
  let nextNode = current.next;
  while (nextNode !== null) {
    current = nextNode;
    nextNode = current.next;
  }
  ```

### 16. NEVER Call Array.get() - Runtime Compatibility
- **CRITICAL RULE**: NEVER call `arr.get(index)` in your code - it will crash at runtime!
- **Explanation**: `Array.get()` exists ONLY for SKJS type checking purposes
- **Reality**: The `.get()` method does not exist on JavaScript arrays at runtime
- **Syntax Sugar**: `arr[index]` is treated as syntactic sugar for `arr.get(index)` by SKJS
- **Runtime Behavior**: `arr[index]` works fine at runtime, `arr.get(index)` will throw "method not found"
- **Example**:
  ```typescript
  let arr: Array<number> = [1, 2, 3];
  
  // CORRECT - works in both SKJS and runtime
  let element = arr[0];
  
  // WRONG - will crash at runtime!
  let element = arr.get(0); // TypeError: arr.get is not a function
  ```
- **Memory Aid**: If you see `.get(` in array code, it's a bug waiting to happen!

### 17. The `any` Type is Not Supported
- **CRITICAL RULE**: NEVER use the `any` type in SKJS code
- **Explanation**: The `any` type is not implemented in the SKJS type checker
- **Error**: Using `any` will cause type checking errors
- **Alternatives**: Use specific types, union types, or generic types instead
- **Example**:
  ```typescript
  // WRONG - will cause errors
  let value: any = "hello";
  
  // CORRECT - use specific types
  let value: string = "hello";
  
  // CORRECT - use union types for multiple possibilities
  let value: string | number = "hello";
  
  // CORRECT - use generics for flexible types
  function process<T>(value: T): T { return value; }
  ```

### 18. Template Literal Strings Not Supported
- **Rule**: Backtick template strings are not implemented
- **Error**: "TODO: support for backtick strings"
- **Workaround**: Use string concatenation with `+` operator
- **Example**:
  ```typescript
  // WRONG - will cause errors
  let message = `Hello ${name}, you are ${age} years old`;
  
  // CORRECT - use string concatenation
  let message = "Hello " + name + ", you are " + age + " years old";
  ```

### 19. Boolean Literal Type Casting Not Supported
- **Rule**: Casting boolean values to literal boolean types is not supported
- **Error**: "Construction not supported" when using `false as false` or `true as true`
- **Workaround**: Use explicit boolean comparisons or different type definitions
- **Example**:
  ```typescript
  // WRONG - will cause errors
  let result: 'true' | 'false' = false as false;
  
  // CORRECT - use conditional expressions
  let result: 'true' | 'false' = condition ? 'true' : 'false';
  ```

### 20. For...of Loops Not Supported  
- **Rule**: For...of loop syntax is not implemented
- **Error**: "TODO: for ... of not implemented, you can use a normal for (for now)"
- **Workaround**: Use traditional for loops with index
- **Example**:
  ```typescript
  // WRONG - will cause errors
  for (let item of items) {
    console.log(item);
  }
  
  // CORRECT - use traditional for loop
  for (let i = 0; i < items.length; i++) {
    const item = items[i];
    if (item !== undefined) {
      console.log(item);
    }
  }
  ```

### 21. In Operator Not Supported
- **Rule**: The `in` operator for type guards is not supported
- **Error**: "Expected )" when using `if ("prop" in obj)`
- **Workaround**: Use instanceof checks or explicit type assertions
- **Example**:
  ```typescript
  // WRONG - will cause errors
  if ("move" in shape) {
    shape.move(10, 10);
  }
  
  // CORRECT - use instanceof
  if (shape instanceof Rectangle) {
    shape.move(10, 10);
  }
  
  // CORRECT - use type assertions
  const moveable = shape as Moveable;
  moveable.move(10, 10);
  ```

## Coding Guidelines for SKJS

1. **Avoid toplevel variables**: Define everything inside functions or classes
2. **Use explicit Array construction**: Don't rely on array literals for typed arrays
3. **Keep constructor signatures simple**: Match parent class constructors exactly
4. **Use single console.log arguments**: Concatenate strings before logging
5. **Avoid private modifiers**: Use public fields only
6. **Handle undefined explicitly**: Check for undefined before method calls
7. **Generic classes work well**: Both generic functions and generic classes are fully supported
8. **Use `new Array<T>()` for array initialization**: This works in all cases including generic classes
9. **Use local variables for null/undefined comparisons**: Always assign properties to locals before comparing to null/undefined
10. **NEVER use Array.get()**: Always use `arr[index]` syntax - `.get()` will crash at runtime!
11. **NEVER use the `any` type**: The `any` type is not supported in SKJS - use specific types or union types instead
12. **Avoid the `!` operator**: Use explicit comparisons like `=== false` instead of `!` for better type safety

## File Organization and Structure Guidelines

### 22. Prefer Small, Focused Files
- **Rule**: Split code into as many separate files as possible
- **Guideline**: Aim for one function per file whenever practical
- **Rationale**: Small files are easier to type-check, debug, and maintain in SKJS
- **Example Structure**:
  ```typescript
  // math_add.ts
  export function add(a: number, b: number): number {
    return a + b;
  }
  
  // math_multiply.ts  
  export function multiply(a: number, b: number): number {
    return a * b;
  }
  
  // math_utils.ts - aggregates multiple utilities
  import { add } from './math_add.js';
  import { multiply } from './math_multiply.js';
  export { add, multiply };
  ```

### 23. Keep Classes Minimal
- **Rule**: Define only core methods in classes (constructor, essential primitives)
- **Guideline**: Move complex logic to separate utility functions
- **Rationale**: Smaller classes are easier to type-check and less prone to SKJS limitations
- **Example**:
  ```typescript
  // user.ts - minimal class
  export class User {
    name: string;
    email: string;
    
    constructor(name: string, email: string) {
      this.name = name;
      this.email = email;
    }
  }
  
  // user_validation.ts - separate utility
  import { User } from './user.js';
  export function validateUser(user: User): boolean {
    return user.name.length > 0 && user.email.includes('@');
  }
  
  // user_formatting.ts - separate utility
  import { User } from './user.js';
  export function formatUserDisplay(user: User): string {
    return user.name + ' (' + user.email + ')';
  }
  ```

### 24. File Size Guidelines
- **Target**: Aim for files under 50 lines when possible
- **Maximum**: Keep files under 100 lines for optimal SKJS performance
- **Benefits**: 
  - Faster type checking
  - Easier debugging
  - Better modularity
  - Reduced complexity per file
- **When to Split**: If a file has multiple functions, consider splitting into separate files

### 25. Logical File Organization
- **Group by Feature**: Create separate files for related functionality
- **Separate Concerns**: Keep types, utilities, and business logic in different files
- **Example Directory Structure**:
  ```
  src/
  ├── types/
  │   ├── user.ts
  │   ├── product.ts
  │   └── order.ts
  ├── utils/
  │   ├── string_utils.ts
  │   ├── math_utils.ts
  │   └── validation_utils.ts
  ├── business/
  │   ├── user_service.ts
  │   ├── order_processing.ts
  │   └── inventory_management.ts
  └── main.ts
  ```

### 26. Import/Export Organization
- **Rule**: Use barrel exports to aggregate related functionality
- **Pattern**: Create index files that re-export from multiple small files
- **Example**:
  ```typescript
  // utils/index.ts
  export { add, subtract } from './math_add.js';
  export { multiply, divide } from './math_multiply.js';
  export { validateEmail } from './email_validator.js';
  
  // main.ts
  import { add, validateEmail } from './utils/index.js';
  ```

### Benefits of Small Files in SKJS
1. **Faster Compilation**: SKJS type-checks smaller files more quickly
2. **Easier Debugging**: Isolated functions are easier to test and debug
3. **Better Modularity**: Encourages clean separation of concerns
4. **Reduced Complexity**: Each file focuses on a single responsibility
5. **Improved Maintainability**: Changes affect smaller, more focused areas
6. **Better Error Localization**: Type errors are easier to locate in small files

## What Works Well in SKJS

- Function generics (`function identity<T>(arg: T): T`)
- Generic classes (`class Stack<T> { ... }`)
- Interface definitions
- Union types (`string | number`)
- Tuple types (`[number, string, boolean]`)
- Algebraic Data Types with `kind` field discrimination
- Import/export system with relative paths
- Basic class definitions
- Method calls with proper type checking
- Explicit type annotations
- String concatenation and basic operations
- Math operations and comparisons

## Recommended Patterns

### Array Creation vs Tuples
```typescript
// Good - Arrays for homogeneous collections
let arr: Array<number> = new Array<number>();
arr.push(1);
arr.push(2);

// Good - Tuples for heterogeneous fixed collections
let tuple: [number, string] = [42, "hello"];
let coordinate: [number, number] = [10, 20];
let userInfo: [string, number, boolean] = ["Alice", 25, true];

// Avoid - mixing array and tuple syntax
let arr: Array<number> = [1, 2]; // Type incompatibility
```

### Class Design
```typescript
// Good - simple class
class Person {
    name: string;
    constructor(name: string) { this.name = name; }
}

// Good - generic classes work well
class Stack<T> {
    items: Array<T>;
    constructor() { this.items = new Array<T>(); }
}

// Good - inheritance with matching constructors
class Student extends Person {
    constructor(name: string, age: number) { super(name, age); }
}

// Avoid - inheritance with different constructor signatures
class Student extends Person {
    constructor(name: string, age: number, id: string) { ... } // Error: signature mismatch
}
```

### Function Organization
```typescript
// Good - everything in functions
function main(): void {
    let x: number = 10;
    console.log(x.toString());
}

// Avoid - toplevel variables
let x: number = 10; // "Construction not supported: toplevel let"
```

### Literal Types and Union Types
```typescript
// Good - use single quotes for literal types
type Status = 'active' | 'inactive' | 'pending';
let userStatus: Status = 'active';

// Good - use double quotes for string values
let message: string = "Hello, world!";

// Avoid - mixing quotes inappropriately
type Status = "active" | "inactive"; // Should use single quotes
let userStatus: Status = "active"; // Should use single quotes
```

### Algebraic Data Types
```typescript
// Good - ADT with 'kind' field
type Shape = 
    | { kind: 'circle', radius: number }
    | { kind: 'square', side: number };

function calculateArea(shape: Shape): number {
    if (shape.kind === 'circle') {
        return Math.PI * shape.radius * shape.radius;
    } else if (shape.kind === 'square') {
        return shape.side * shape.side;
    }
    return 0;
}

// Avoid - using different discriminator field
type BadShape = 
    | { type: 'circle', radius: number }  // Won't enable pattern matching
    | { type: 'square', side: number };
```

### Import/Export System
```typescript
// Good - proper import syntax
import { add, multiply, User } from './math_utils.js';
import { Result, Option } from './types.js';

// Export functions and types
export function helper(): void { ... }
export type MyType = { ... };
export interface MyInterface { ... }

// Avoid - incorrect import paths
import { add } from 'math_utils';        // Missing ./ and .js
import { add } from './math_utils';      // Missing .js extension
import { add } from './math_utils.ts';   // Wrong extension
```

### Null/Undefined Comparison Patterns
```typescript
// Good - compare local variables to null/undefined
function processUser(user: { name: string | null, age: number | null }): void {
    let name = user.name;
    let age = user.age;
    
    if (name != null) {
        console.log(name.toUpperCase()); // Works: local comparison
    }
    
    if (age != null) {
        console.log(age.toString()); // Works: local comparison
    }
}

// Good - handle linked list traversal with locals
function traverseList<T>(head: ListNode<T> | null): void {
    let current = head;
    let nextNode = current?.next;
    
    while (nextNode !== null) {
        current = nextNode;
        nextNode = current.next;
    }
}

// Good - handle union types with local assignment
function handleResponse(response: { data: string } | { error: string }): void {
    let data = response.data;
    let error = response.error;
    
    if (data != null) {
        console.log(data); // Works: local comparison
    } else if (error != null) {
        console.log(error); // Works: local comparison
    }
}

// Avoid - comparing property access directly to null/undefined
function badProcessUser(user: { name: string | null }): void {
    if (user.name != null) { // Error: "Only locals can be compared to null/undefined"
        console.log(user.name.toUpperCase());
    }
}

// Avoid - comparing property in loops
function badTraverseList<T>(head: ListNode<T> | null): void {
    let current = head;
    while (current.next !== null) { // Error: property comparison to null
        current = current.next;
    }
}
```

## Working Examples Summary

The following TypeScript files demonstrate patterns that work well with SKJS:

### Basic Examples
- **basic_types.ts**: Variable declarations, functions, basic types
- **classes.ts**: Class definitions without inheritance
- **algorithms.ts**: Array operations, recursive algorithms

### Advanced Examples  
- **advanced.ts**: Interfaces, generics, union types, type annotations
- **generic_examples.ts**: Comprehensive generic classes (Container, Collection, Stack, Pair)
- **tuple_examples.ts**: Tuple types, mixed-type collections, tuple operations
- **simple_adt_examples.ts**: Algebraic Data Types with `kind` field pattern matching
- **state_machines.ts**: State machine patterns using ADTs and pattern matching
- **working_patterns.ts**: Practical patterns - branded types, Result type, validation
- **data_structures.ts**: Stack implementations with concrete types
- **functional_programming.ts**: Map, filter, reduce, function composition
- **recursion_examples.ts**: Factorial, Fibonacci, string reversal
- **string_processing.ts**: String manipulation, palindrome checking
- **edge_cases.ts**: Optional parameters, null checks, boundary conditions
- **complex_types.ts**: Type aliases, nested interfaces, type-safe operations
- **mathematical_computations.ts**: Prime numbers, matrix operations, statistics

### Module System Examples
- **math_utils.ts**: Exportable math functions and utilities
- **array_utils.ts**: Array manipulation functions for import/export
- **types.ts**: Shared type definitions and interfaces
- **result_utils.ts**: Result type utilities with validation functions
- **business_logic.ts**: Complex business logic using multiple imports
- **import_demo.ts**: Comprehensive demonstration of the import system

### Enhanced Builtins
The builtins.ts file has been extended with:
- Additional Array methods: `filter`, `reduce`, `join`, `slice`
- More Math functions: `min`, `ceil`, `round`, `abs`, `pow`, `sqrt`
- Extended string methods: `substring`, `indexOf`, `split`, `toLowerCase`, `toUpperCase`

All examples follow SKJS constraints and pass type checking successfully.
