///////////////////////////////////////////////////////////////////////////////
// Unit tests for the type-checker. All these tests are supposed to succeed.
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic intersection and union properties
///////////////////////////////////////////////////////////////////////////////

function generic<T1, T2>(arg: T1 & T2): T1 {
  return arg;
}

function generic2<T1, T2>(arg: T1 & T2): T2 {
  return arg;
}

function generic3<T1, T2>(arg: T1): T1 | T2 {
  return arg;
}

function generic4<T1, T2>(arg: T2): T1 | T2 {
  return arg;
}

///////////////////////////////////////////////////////////////////////////////
// Objects
///////////////////////////////////////////////////////////////////////////////

function checkObject(obj: { field1: number }): {} {
  return obj;
}

function checkObject2(obj: { field1: number }): { field1: number } {
  return obj;
}

function checkObject3(obj: { field1: number } & { field2: number }): {
  field1: number;
  field2: number;
} {
  return obj;
}

function checkObject4(obj: { field1: number } | { field2: number }): {} {
  return obj;
}

function checkObject5(
  obj: { field1: number } | { field1: number; field2: number },
): { field1: number } {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Algebraic data types
///////////////////////////////////////////////////////////////////////////////

type adt = { kind: "tag1"; field1: boolean } | { kind: "tag2"; field2: number };

function check(data: adt): boolean {
  if (data.kind === "tag1") return data.field1;
  return false;
}

///////////////////////////////////////////////////////////////////////////////
// Tuples
///////////////////////////////////////////////////////////////////////////////

function check2(t1: [number, boolean]): number {
  return t1[0];
}

function check3(t1: [number, boolean]): boolean {
  return t1[1];
}

// Mutable tuples are invariant in their element types, so a union of
// distinct element types does not subtype a pointwise-unioned tuple.
function check4(t1: [number] | [boolean]): [number | boolean] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return t1;
}

function check5(t1: [number] | [boolean]): number | boolean {
  let [x] = t1;
  return x;
}

function check6(
  t1: [{ field1: number }] & [{ field2: boolean }],
): [{ field1: number; field2: boolean }] {
  return t1;
}

function checkTuple(tuple: [number, string]): [number, string] {
  return tuple;
}

function checkTuple2(
  tuple: [number, string] | [string, number],
): [number | string, number | string] {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return tuple;
}

function checkTuple3(
  tuple: [number, string, boolean],
): [number, string, boolean] {
  return tuple;
}

///////////////////////////////////////////////////////////////////////////////
// consts
///////////////////////////////////////////////////////////////////////////////

const x: number = 0;

function check7(): number {
  return x;
}

const n: 0 = 0;

function check8(): 0 {
  return n;
}

const n2 = 1;

function check9(): 0 | 1 {
  if (true) return n2;
  return n;
}

const s = "hello";

function check10(): "hello" {
  return s;
}

const b = true;

function check11(): true {
  return b;
}

///////////////////////////////////////////////////////////////////////////////
// Arrays
///////////////////////////////////////////////////////////////////////////////

function checkArray(arr: number[]): number[] {
  return arr;
}

function checkArray2(arr: (number | string)[]): (number | string)[] {
  return arr;
}

function checkArray3(arr: (number & string)[]): never[] {
  return arr;
}

///////////////////////////////////////////////////////////////////////////////
// Functions
///////////////////////////////////////////////////////////////////////////////

function checkFunction(func: (x: number) => number): (x: number) => number {
  return func;
}

function checkFunction2(
  func: (x: number) => number | string,
): (x: number) => number | string {
  return func;
}

function checkFunction3(
  func: (x: number) => number & string,
): (x: number) => never {
  return func;
}

///////////////////////////////////////////////////////////////////////////////
// Type Literals
///////////////////////////////////////////////////////////////////////////////

type LiteralType1 = { field1: number };
type LiteralType2 = { field2: string };

function checkLiteralType(
  obj: LiteralType1 & LiteralType2,
): LiteralType1 & LiteralType2 {
  return obj;
}

function checkLiteralType2(
  obj: LiteralType1 | LiteralType2,
): LiteralType1 | LiteralType2 {
  return obj;
}

function checkLiteralType3(obj: {
  field1: number;
  field2: string;
}): LiteralType1 & LiteralType2 {
  return obj;
}

function checkLiteralType4(
  obj: { field1: number } | { field2: string },
): LiteralType1 | LiteralType2 {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Complex Nested Types
///////////////////////////////////////////////////////////////////////////////

type NestedType1 = { a: { b: { c: number } } };
type NestedType2 = { a: { b: { d: string } } };

function checkNestedTypeIntersection(obj: NestedType1 & NestedType2): {
  a: { b: { c: number; d: string } };
} {
  // Would be correct if the objects were readonly
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return obj;
}

function checkNestedType2(obj: NestedType1 | NestedType2): {
  a: { b: { c?: number; d?: string } };
} {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Type Aliases and Interfaces
///////////////////////////////////////////////////////////////////////////////

type AliasType = { field: number };
interface InterfaceType {
  field: number;
}

function checkAlias(obj: AliasType): AliasType {
  return obj;
}

function checkInterface(obj: InterfaceType): InterfaceType {
  return obj;
}

function checkAliasAndInterface(obj: AliasType & InterfaceType): {
  field: number;
} {
  return obj;
}

function checkAliasOrInterface(obj: AliasType | InterfaceType): {
  field: number;
} {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Interfaces
///////////////////////////////////////////////////////////////////////////////

interface SimpleInterface {
  field1: number;
  field2: string;
}

interface ExtendedInterface extends SimpleInterface {
  field3: boolean;
}

interface AnotherInterface {
  field4: number;
}

function checkSimpleInterface(obj: SimpleInterface): SimpleInterface {
  return obj;
}

function checkExtendedInterface(obj: ExtendedInterface): ExtendedInterface {
  return obj;
}

function checkAnotherInterface(obj: AnotherInterface): AnotherInterface {
  return obj;
}

function checkIntersectionInterface(
  obj: SimpleInterface & AnotherInterface,
): SimpleInterface & AnotherInterface {
  return obj;
}

function checkUnionInterface(
  obj: SimpleInterface | AnotherInterface,
): SimpleInterface | AnotherInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Extending Interfaces and Type Aliases
///////////////////////////////////////////////////////////////////////////////

interface AliasWithInterface extends SimpleInterface {
  field5: string;
}

interface InterfaceWithAlias extends AliasWithInterface {
  field6: boolean;
}

function checkAliasWithInterface(obj: AliasWithInterface): AliasWithInterface {
  return obj;
}

function checkInterfaceWithAlias(obj: InterfaceWithAlias): InterfaceWithAlias {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Interface Implementations
///////////////////////////////////////////////////////////////////////////////

class ClassImplementingInterface implements SimpleInterface {
  field1: number;
  field2: string;
  constructor(field1: number, field2: string) {
    this.field1 = field1;
    this.field2 = field2;
  }
}

class ClassImplementingExtendedInterface implements ExtendedInterface {
  field1: number;
  field2: string;
  field3: boolean;
  constructor(field1: number, field2: string, field3: boolean) {
    this.field1 = field1;
    this.field2 = field2;
    this.field3 = field3;
  }
}

function checkClassImplementingInterface(
  obj: ClassImplementingInterface,
): SimpleInterface {
  return obj;
}

function checkClassImplementingExtendedInterface(
  obj: ClassImplementingExtendedInterface,
): ExtendedInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Interface and Type Combinations
///////////////////////////////////////////////////////////////////////////////

type CombinationType1 = SimpleInterface & { field7: string };
type CombinationType2 = SimpleInterface | { field8: boolean };

function checkCombinationType1(obj: CombinationType1): CombinationType1 {
  return obj;
}

function checkCombinationType2(obj: CombinationType2): CombinationType2 {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Complex Interface Hierarchies
///////////////////////////////////////////////////////////////////////////////

interface BaseInterface {
  baseField: number;
}

interface DerivedInterface1 extends BaseInterface {
  derivedField1: string;
}

interface DerivedInterface2 extends BaseInterface {
  derivedField2: boolean;
}

interface CombinedDerivedInterface
  extends DerivedInterface1,
    DerivedInterface2 {}

function checkBaseInterface(obj: BaseInterface): BaseInterface {
  return obj;
}

function checkDerivedInterface1(obj: DerivedInterface1): DerivedInterface1 {
  return obj;
}

function checkDerivedInterface2(obj: DerivedInterface2): DerivedInterface2 {
  return obj;
}

function checkCombinedDerivedInterface(
  obj: CombinedDerivedInterface,
): CombinedDerivedInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Constructor Initialization Checks
///////////////////////////////////////////////////////////////////////////////

interface InitSimpleInterface {
  field1: number;
  field2: string;
}

class ClassWithConstructor implements InitSimpleInterface {
  field1: number;
  field2: string;
  constructor(field1: number, field2: string) {
    this.field1 = field1;
    this.field2 = field2;
  }
}

function checkClassWithConstructor(
  obj: ClassWithConstructor,
): InitSimpleInterface {
  return obj;
}

interface InitExtendedInterface extends InitSimpleInterface {
  field3: boolean;
}

class ClassWithExtendedConstructor implements InitExtendedInterface {
  field1: number;
  field2: string;
  field3: boolean;
  constructor(field1: number, field2: string, field3: boolean) {
    this.field1 = field1;
    this.field2 = field2;
    this.field3 = field3;
  }
}

function checkClassWithExtendedConstructor(
  obj: ClassWithExtendedConstructor,
): InitExtendedInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Complex Initialization Checks
///////////////////////////////////////////////////////////////////////////////

interface InitComplexInterface {
  nested: {
    field1: number;
    field2: string;
  };
  list: number[];
}

class ClassWithComplexConstructor implements InitComplexInterface {
  nested: {
    field1: number;
    field2: string;
  };
  list: number[];
  constructor(field1: number, field2: string, list: number[]) {
    this.nested = { field1, field2 };
    this.list = list;
  }
}

function checkClassWithComplexConstructor(
  obj: ClassWithComplexConstructor,
): InitComplexInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Interface and Type Combinations with Initialization
///////////////////////////////////////////////////////////////////////////////

interface InitAliasWithInterface extends InitSimpleInterface {
  field4: string;
}

class ClassWithAliasConstructor implements InitAliasWithInterface {
  field1: number;
  field2: string;
  field4: string;
  constructor(field1: number, field2: string, field4: string) {
    this.field1 = field1;
    this.field2 = field2;
    this.field4 = field4;
  }
}

function checkClassWithAliasConstructor(
  obj: ClassWithAliasConstructor,
): InitAliasWithInterface {
  return obj;
}

interface InitInterfaceWithAlias extends InitAliasWithInterface {
  field5: boolean;
}

class ClassWithInterfaceAliasConstructor implements InitInterfaceWithAlias {
  field1: number;
  field2: string;
  field4: string;
  field5: boolean;
  constructor(field1: number, field2: string, field4: string, field5: boolean) {
    this.field1 = field1;
    this.field2 = field2;
    this.field4 = field4;
    this.field5 = field5;
  }
}

function checkClassWithInterfaceAliasConstructor(
  obj: ClassWithInterfaceAliasConstructor,
): InitInterfaceWithAlias {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Multiple Interface Implementation
///////////////////////////////////////////////////////////////////////////////

interface Interface1 {
  field1: number;
}

interface Interface2 {
  field2: string;
}

class ClassImplementingMultipleInterfaces implements Interface1, Interface2 {
  field1: number;
  field2: string;
  constructor(field1: number, field2: string) {
    this.field1 = field1;
    this.field2 = field2;
  }
}

function checkClassImplementingMultipleInterfaces(
  obj: ClassImplementingMultipleInterfaces,
): Interface1 & Interface2 {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Complex Interface Hierarchies with Initialization
///////////////////////////////////////////////////////////////////////////////

interface InitBaseInterface {
  baseField: number;
}

interface InitDerivedInterface1 extends InitBaseInterface {
  derivedField1: string;
}

interface InitDerivedInterface2 extends InitBaseInterface {
  derivedField2: boolean;
}

interface InitCombinedDerivedInterface
  extends InitDerivedInterface1,
    InitDerivedInterface2 {}

class ClassWithCombinedDerivedConstructor
  implements InitCombinedDerivedInterface
{
  baseField: number;
  derivedField1: string;
  derivedField2: boolean;
  constructor(
    baseField: number,
    derivedField1: string,
    derivedField2: boolean,
  ) {
    this.baseField = baseField;
    this.derivedField1 = derivedField1;
    this.derivedField2 = derivedField2;
  }
}

function checkClassWithCombinedDerivedConstructor(
  obj: ClassWithCombinedDerivedConstructor,
): InitCombinedDerivedInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Initialization Checks with Optional Fields
//
// Optional fields are EXACT (present => T): a constructor that
// unconditionally assigns an optional parameter makes the field present
// with a possibly-undefined value, so these declarations carry
// `| undefined` explicitly (see optional-fields-exact.ts).
///////////////////////////////////////////////////////////////////////////////

interface OptionalFieldsInterface {
  field1: number;
  field2?: string | undefined;
}

class ClassWithOptionalFields implements OptionalFieldsInterface {
  field1: number;
  field2?: string | undefined;
  constructor(field1: number, field2?: string) {
    this.field1 = field1;
    this.field2 = field2;
  }
}

function checkClassWithOptionalFields(
  obj: ClassWithOptionalFields,
): OptionalFieldsInterface {
  return obj;
}

interface ExtendedOptionalFieldsInterface extends OptionalFieldsInterface {
  field3?: boolean | undefined;
}

class ClassWithExtendedOptionalFields
  implements ExtendedOptionalFieldsInterface
{
  field1: number;
  field2?: string | undefined;
  field3?: boolean | undefined;
  constructor(field1: number, field2?: string, field3?: boolean) {
    this.field1 = field1;
    this.field2 = field2;
    this.field3 = field3;
  }
}

function checkClassWithExtendedOptionalFields(
  obj: ClassWithExtendedOptionalFields,
): ExtendedOptionalFieldsInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Complex Initialization with Optional Fields
///////////////////////////////////////////////////////////////////////////////

interface ComplexOptionalFieldsInterface {
  nested?:
    | {
        field1: number;
        field2?: string;
      }
    | undefined;
  list?: number[] | undefined;
}

class ClassWithComplexOptionalFields implements ComplexOptionalFieldsInterface {
  nested?:
    | {
        field1: number;
        field2?: string;
      }
    | undefined;
  list?: number[] | undefined;
  constructor(nested?: { field1: number; field2?: string }, list?: number[]) {
    this.nested = nested;
    this.list = list;
  }
}

function checkClassWithComplexOptionalFields(
  obj: ClassWithComplexOptionalFields,
): ComplexOptionalFieldsInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Interface and Type Combinations with Optional Fields
///////////////////////////////////////////////////////////////////////////////

interface OptionalAliasWithInterface extends OptionalFieldsInterface {
  field4?: string | undefined;
}

class ClassWithOptionalAliasConstructor implements OptionalAliasWithInterface {
  field1: number;
  field2?: string | undefined;
  field4?: string | undefined;
  constructor(field1: number, field2?: string, field4?: string) {
    this.field1 = field1;
    this.field2 = field2;
    this.field4 = field4;
  }
}

function checkClassWithOptionalAliasConstructor(
  obj: ClassWithOptionalAliasConstructor,
): OptionalAliasWithInterface {
  return obj;
}

interface OptionalInterfaceWithAlias extends OptionalAliasWithInterface {
  field5?: boolean | undefined;
}

class ClassWithOptionalInterfaceAliasConstructor
  implements OptionalInterfaceWithAlias
{
  field1: number;
  field2?: string | undefined;
  field4?: string | undefined;
  field5?: boolean | undefined;
  constructor(
    field1: number,
    field2?: string,
    field4?: string,
    field5?: boolean,
  ) {
    this.field1 = field1;
    this.field2 = field2;
    this.field4 = field4;
    this.field5 = field5;
  }
}

function checkClassWithOptionalInterfaceAliasConstructor(
  obj: ClassWithOptionalInterfaceAliasConstructor,
): OptionalInterfaceWithAlias {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Multiple Interface Implementation with Optional Fields
///////////////////////////////////////////////////////////////////////////////

interface OptionalInterface1 {
  field1: number;
  field2?: string | undefined;
}

interface OptionalInterface2 {
  field3?: boolean | undefined;
}

class ClassImplementingOptionalInterfaces
  implements OptionalInterface1, OptionalInterface2
{
  field1: number;
  field2?: string | undefined;
  field3?: boolean | undefined;
  constructor(field1: number, field2?: string, field3?: boolean) {
    this.field1 = field1;
    this.field2 = field2;
    this.field3 = field3;
  }
}

function checkClassImplementingOptionalInterfaces(
  obj: ClassImplementingOptionalInterfaces,
): OptionalInterface1 & OptionalInterface2 {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Complex Interface Hierarchies with Optional Fields
///////////////////////////////////////////////////////////////////////////////

interface OptionalBaseInterface {
  baseField: number;
  optionalBaseField?: string | undefined;
}

interface OptionalDerivedInterface1 extends OptionalBaseInterface {
  derivedField1: string;
  optionalDerivedField1?: boolean | undefined;
}

interface OptionalDerivedInterface2 extends OptionalBaseInterface {
  derivedField2: boolean;
  optionalDerivedField2?: string | undefined;
}

interface OptionalCombinedDerivedInterface
  extends OptionalDerivedInterface1,
    OptionalDerivedInterface2 {}

class ClassWithOptionalCombinedDerivedConstructor
  implements OptionalCombinedDerivedInterface
{
  baseField: number;
  optionalBaseField?: string | undefined;
  derivedField1: string;
  optionalDerivedField1?: boolean | undefined;
  derivedField2: boolean;
  optionalDerivedField2?: string | undefined;
  constructor(
    baseField: number,
    derivedField1: string,
    derivedField2: boolean,
    optionalBaseField?: string,
    optionalDerivedField1?: boolean,
    optionalDerivedField2?: string,
  ) {
    this.baseField = baseField;
    this.optionalBaseField = optionalBaseField;
    this.derivedField1 = derivedField1;
    this.optionalDerivedField1 = optionalDerivedField1;
    this.derivedField2 = derivedField2;
    this.optionalDerivedField2 = optionalDerivedField2;
  }
}

function checkClassWithOptionalCombinedDerivedConstructor(
  obj: ClassWithOptionalCombinedDerivedConstructor,
): OptionalCombinedDerivedInterface {
  return obj;
}

interface ConditionalInterface {
  field1: number;
  field2: string;
}

class ClassWithIfElse {
  field1: number;
  field2: string;
  constructor(field1: number, field2: string) {
    if (field1 > 0) {
      this.field1 = field1;
      this.field2 = field2;
    } else {
      this.field1 = 0;
      this.field2 = "default";
    }
  }
}

function checkClassWithIfElse(obj: ClassWithIfElse): ConditionalInterface {
  return obj;
}

///////////////////////////////////////////////////////////////////////////////
// Typeof
///////////////////////////////////////////////////////////////////////////////

function checkTypeofUndefined(): typeof undefined {
  return undefined;
}

///////////////////////////////////////////////////////////////////////////////
// Conditional Expressions Type-Checking
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// If/Else Statements
///////////////////////////////////////////////////////////////////////////////

function checkIfElseExpression(input: number | string): number {
  if (typeof input === "number") {
    return input;
  } else {
    return 0;
  }
}

function checkIfElseExpressionString(input: number | string): string {
  if (typeof input === "string") {
    return input;
  } else {
    return "";
  }
}

///////////////////////////////////////////////////////////////////////////////
// Ternary Operators
///////////////////////////////////////////////////////////////////////////////

/*
function checkTernaryExpression(input: boolean): number {
  return input ? 1 : 0;
}

function checkTernaryExpression2(input: boolean): string {
  return input ? "true" : "false";
}

function checkTernaryExpression3(input: number): number | string {
  return input > 0 ? input : "negative";
}
*/

///////////////////////////////////////////////////////////////////////////////
// Switch Statements
///////////////////////////////////////////////////////////////////////////////

/*
function checkSwitchExpression(value: number): string {
  switch (value) {
    case 1:
      return "one";
    case 2:
      return "two";
    default:
      return "other";
  }
}

function checkSwitchExpression2(value: number | string): number {
  switch (typeof value) {
    case "number":
      return value;
    case "string":
      return value.length;
    default:
      return 0;
  }
}
*/

///////////////////////////////////////////////////////////////////////////////
// Nested Conditionals
///////////////////////////////////////////////////////////////////////////////

/*
function checkNestedConditionals(input: number | string | boolean): string {
  if (typeof input === 'number') {
    return input > 0 ? "positive" : "non-positive";
  } else if (typeof input === 'string') {
    return input.length > 5 ? "long" : "short";
  } else {
    return input ? "true" : "false";
  }
}
*/

///////////////////////////////////////////////////////////////////////////////
// Variable Initialization Checks
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// If/Else Initialization
///////////////////////////////////////////////////////////////////////////////

interface MyType {
  field1: number;
  field2: string;
}

function checkIfElseInitialization(input: boolean): MyType {
  let x: MyType;
  if (input) {
    x = { field1: 1, field2: "true" };
  } else {
    x = { field1: 0, field2: "false" };
  }
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Ternary Operator Initialization
///////////////////////////////////////////////////////////////////////////////

/*
function checkTernaryInitialization(input: boolean): MyType {
  let x: MyType = input ? { field1: 1, field2: "true" } : { field1: 0, field2: "false" };
  return x;
}
*/

///////////////////////////////////////////////////////////////////////////////
// Switch Statement Initialization
///////////////////////////////////////////////////////////////////////////////

/*
function checkSwitchInitialization(value: number): MyType {
  let x: MyType;
  switch (value) {
    case 1:
      x = { field1: 1, field2: "one" };
      break;
    case 2:
      x = { field1: 2, field2: "two" };
      break;
    default:
      x = { field1: 0, field2: "default" };
  }
  return x;
}
*/

///////////////////////////////////////////////////////////////////////////////
// Nested Conditional Initialization
///////////////////////////////////////////////////////////////////////////////

function checkNestedConditionalInitialization(input: number | string): MyType {
  let x: MyType;
  if (typeof input === "number") {
    if (input > 0) {
      x = { field1: input, field2: "positive" };
    } else {
      x = { field1: input, field2: "non-positive" };
    }
  } else {
    if (true) {
      x = { field1: 0, field2: "long" };
    } else {
      x = { field1: 0, field2: "short" };
    }
  }
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Type Guard Initialization
///////////////////////////////////////////////////////////////////////////////

type ComplexType = { kind: "A"; value: number } | { kind: "B"; value: string };

function checkTypeGuardInitialization(obj: ComplexType): MyType {
  let x: MyType;
  if (obj.kind === "A") {
    x = { field1: obj.value, field2: "type A" };
  } else {
    x = { field1: 0, field2: "type B" };
  }
  return x;
}

///////////////////////////////////////////////////////////////////////////////
// Closure Type-Checking
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic Closure
///////////////////////////////////////////////////////////////////////////////

function checkBasicClosure(input: number): () => number {
  let x = input;
  return () => x;
}

function checkBasicClosureString(input: string): () => string {
  let x = input;
  return () => x;
}

///////////////////////////////////////////////////////////////////////////////
// Closure with Nested Functions
///////////////////////////////////////////////////////////////////////////////

function checkNestedFunctionClosure(input: number): () => () => number {
  let x = input;
  return () => {
    let y = x * 2;
    return () => y;
  };
}

function checkNestedFunctionClosureString(input: string): () => () => string {
  let x = input;
  return () => {
    let y = x;
    return () => y;
  };
}

///////////////////////////////////////////////////////////////////////////////
// Closure Capturing External Variables
///////////////////////////////////////////////////////////////////////////////

function checkExternalVariableClosure(): () => number {
  let externalVar = 42;
  return () => externalVar;
}

function checkExternalVariableClosureString(): () => string {
  let externalVar = "hello";
  return () => externalVar;
}

///////////////////////////////////////////////////////////////////////////////
// Closure Returning Objects
///////////////////////////////////////////////////////////////////////////////

interface MyObject {
  field1: number;
  field2: string;
}

function checkObjectClosure(input: number, str: string): () => MyObject {
  let x: MyObject = { field1: input, field2: str };
  return () => x;
}

///////////////////////////////////////////////////////////////////////////////
// Closure with Type Guards
///////////////////////////////////////////////////////////////////////////////

type MyType2 = { kind: "A"; value: number } | { kind: "B"; value: string };

function checkTypeGuardClosure(input: MyType2): () => string {
  let x: string;
  if (input.kind === "A") {
    x = "Type A";
  } else {
    x = "Type B";
  }
  return () => x;
}

///////////////////////////////////////////////////////////////////////////////
// Closure with Generics
///////////////////////////////////////////////////////////////////////////////

function checkGenericClosure<T>(input: T): () => T {
  let x = input;
  return () => x;
}

function checkGenericClosureNumber(input: number): () => number {
  return checkGenericClosure<number>(input);
}

function checkGenericClosureString(input: string): () => string {
  return checkGenericClosure<string>(input);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Closure Inference Type-Checking
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Generic Closure with Parameters
///////////////////////////////////////////////////////////////////////////////

function checkGenericClosureWithParam<T>(input: T): (arg: T) => T {
  return (arg: T) => arg;
}

function checkGenericClosureWithParamNumber(
  input: number,
): (arg: number) => number {
  return checkGenericClosureWithParam<number>(input);
}

function checkGenericClosureWithParamString(
  input: string,
): (arg: string) => string {
  return checkGenericClosureWithParam<string>(input);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Closure with Multiple Parameters
///////////////////////////////////////////////////////////////////////////////

function checkGenericClosureWithMultipleParams<T1, T2>(
  input1: T1,
  input2: T2,
): (arg1: T1, arg2: T2) => [T1, T2] {
  return (arg1: T1, arg2: T2) => [arg1, arg2];
}

function checkGenericClosureWithMultipleParamsNumberString(
  input1: number,
  input2: string,
): (arg1: number, arg2: string) => [number, string] {
  return checkGenericClosureWithMultipleParams<number, string>(input1, input2);
}

function checkGenericClosureWithMultipleParamsBooleanObject(
  input1: boolean,
  input2: { field: string },
): (arg1: boolean, arg2: { field: string }) => [boolean, { field: string }] {
  return checkGenericClosureWithMultipleParams<boolean, { field: string }>(
    input1,
    input2,
  );
}

///////////////////////////////////////////////////////////////////////////////
// Generic Closure with Array Parameters
///////////////////////////////////////////////////////////////////////////////

function checkGenericClosureWithArrayParam<T>(input: T[]): (arg: T[]) => T[] {
  return (arg: T[]) => arg;
}

function checkGenericClosureWithArrayParamNumber(
  input: number[],
): (arg: number[]) => number[] {
  return checkGenericClosureWithArrayParam<number>(input);
}

function checkGenericClosureWithArrayParamString(
  input: string[],
): (arg: string[]) => string[] {
  return checkGenericClosureWithArrayParam<string>(input);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Closure with Object Parameters
///////////////////////////////////////////////////////////////////////////////

function checkGenericClosureWithObjectParam<T>(
  input: ComplexObject<T>,
): (arg: ComplexObject<T>) => ComplexObject<T> {
  return (arg: ComplexObject<T>) => arg;
}

function checkGenericClosureWithObjectParamNumber(
  input: ComplexObject<number>,
): (arg: ComplexObject<number>) => ComplexObject<number> {
  return checkGenericClosureWithObjectParam<number>(input);
}

function checkGenericClosureWithObjectParamString(
  input: ComplexObject<string>,
): (arg: ComplexObject<string>) => ComplexObject<string> {
  return checkGenericClosureWithObjectParam<string>(input);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Closure with Constraints
///////////////////////////////////////////////////////////////////////////////

function checkConstrainedGenericClosureWithParam<T extends { length: number }>(
  input: T,
): (arg: T) => number {
  return (arg: T) => arg.length;
}

function checkConstrainedGenericClosureWithParamString(
  input: string,
): (arg: string) => number {
  // @skjs-expect-error Type argument does not satisfy the constraint
  return checkConstrainedGenericClosureWithParam<string>(input);
}

function checkConstrainedGenericClosureWithParamArray(input: {
  length: number;
}): (arg: { length: number }) => number {
  return checkConstrainedGenericClosureWithParam<{ length: number }>(input);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Closure with Multiple Type Parameters and Constraints
///////////////////////////////////////////////////////////////////////////////

function checkMultipleConstrainedGenericClosureWithParam<
  T1 extends { length: number },
  T2 extends { size: number },
>(input1: T1, input2: T2): (arg1: T1, arg2: T2) => [number, number] {
  return (arg1: T1, arg2: T2) => [arg1.length, arg2.size];
}

function checkMultipleConstrainedGenericClosureWithParamStringArray(
  input1: string,
  input2: { size: number },
): (arg1: string, arg2: { size: number }) => [number, number] {
  // @skjs-expect-error Type argument does not satisfy the constraint
  return checkMultipleConstrainedGenericClosureWithParam<
    string,
    { size: number }
  >(input1, input2);
}

function checkMultipleConstrainedGenericClosureWithParamObjectArray(
  input1: { length: number },
  input2: { size: number },
): (arg1: { length: number }, arg2: { size: number }) => [number, number] {
  return checkMultipleConstrainedGenericClosureWithParam<
    { length: number },
    { size: number }
  >(input1, input2);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Top-Level Functions with Optional Parameters Type-Checking
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Basic Generic Function with Optional Parameters
///////////////////////////////////////////////////////////////////////////////

function checkGenericFunctionWithOptionalParam<T>(
  input: T,
  arg?: T,
): T | undefined {
  return arg;
}

function checkGenericFunctionWithOptionalParamNumber(
  input: number,
  arg?: number,
): number | undefined {
  return checkGenericFunctionWithOptionalParam<number>(input, arg);
}

function checkGenericFunctionWithOptionalParamString(
  input: string,
  arg?: string,
): string | undefined {
  return checkGenericFunctionWithOptionalParam<string>(input, arg);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Function with Multiple Optional Parameters
///////////////////////////////////////////////////////////////////////////////

function checkGenericFunctionWithMultipleOptionalParams<T1, T2>(
  input1: T1,
  input2: T2,
  arg1?: T1,
  arg2?: T2,
): [T1 | undefined, T2 | undefined] {
  return [arg1, arg2];
}

function checkGenericFunctionWithMultipleOptionalParamsNumberString(
  input1: number,
  input2: string,
  arg1?: number,
  arg2?: string,
): [number | undefined, string | undefined] {
  return checkGenericFunctionWithMultipleOptionalParams<number, string>(
    input1,
    input2,
    arg1,
    arg2,
  );
}

function checkGenericFunctionWithMultipleOptionalParamsBooleanObject(
  input1: boolean,
  input2: { field: string },
  arg1?: boolean,
  arg2?: { field: string },
): [boolean | undefined, { field: string } | undefined] {
  return checkGenericFunctionWithMultipleOptionalParams<
    boolean,
    { field: string }
  >(input1, input2, arg1, arg2);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Function with Optional Array Parameters
///////////////////////////////////////////////////////////////////////////////

function checkGenericFunctionWithOptionalArrayParam<T>(
  input: T[],
  arg?: T[],
): T[] | undefined {
  return arg;
}

function checkGenericFunctionWithOptionalArrayParamNumber(
  input: number[],
  arg?: number[],
): number[] | undefined {
  return checkGenericFunctionWithOptionalArrayParam<number>(input, arg);
}

function checkGenericFunctionWithOptionalArrayParamString(
  input: string[],
  arg?: string[],
): string[] | undefined {
  return checkGenericFunctionWithOptionalArrayParam<string>(input, arg);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Function with Optional Object Parameters
///////////////////////////////////////////////////////////////////////////////

interface ComplexObject<T> {
  value: T;
  description: string;
}

function checkGenericFunctionWithOptionalObjectParam<T>(
  input: ComplexObject<T>,
  arg?: ComplexObject<T>,
): ComplexObject<T> | undefined {
  return arg;
}

function checkGenericFunctionWithOptionalObjectParamNumber(
  input: ComplexObject<number>,
  arg?: ComplexObject<number>,
): ComplexObject<number> | undefined {
  return checkGenericFunctionWithOptionalObjectParam<number>(input, arg);
}

function checkGenericFunctionWithOptionalObjectParamString(
  input: ComplexObject<string>,
  arg?: ComplexObject<string>,
): ComplexObject<string> | undefined {
  return checkGenericFunctionWithOptionalObjectParam<string>(input, arg);
}

///////////////////////////////////////////////////////////////////////////////
// Generic Function with Optional Parameters and Constraints
///////////////////////////////////////////////////////////////////////////////

function checkConstrainedGenericFunctionWithOptionalParam<
  T extends { length: number },
>(input: T, arg?: T): number | undefined {
  if (arg === undefined) return undefined;
  return 0;
}

function checkConstrainedGenericFunctionWithOptionalParamString(
  input: string,
  arg?: string,
): number | undefined {
  // @skjs-expect-error Type argument does not satisfy the constraint
  return checkConstrainedGenericFunctionWithOptionalParam<string>(input, arg);
}

function checkConstrainedGenericFunctionWithOptionalParamArray(
  input: { length: number },
  arg?: { length: number },
): number | undefined {
  return checkConstrainedGenericFunctionWithOptionalParam<{ length: number }>(
    input,
    arg,
  );
}

///////////////////////////////////////////////////////////////////////////////
// Generic Function with Multiple Optional Type Parameters and Constraints
///////////////////////////////////////////////////////////////////////////////

function checkMultipleConstrainedGenericFunctionWithOptionalParam<
  T1 extends { length: number },
  T2 extends { size: number },
>(
  input1: T1,
  input2: T2,
  arg1?: T1,
  arg2?: T2,
): [number | undefined, number | undefined] {
  return [0, 0];
}

function checkMultipleConstrainedGenericFunctionWithOptionalParamStringArray(
  input1: string,
  input2: { size: number },
  arg1?: string,
  arg2?: { size: number },
): [number | undefined, number | undefined] {
  // @skjs-expect-error Type argument does not satisfy the constraint
  return checkMultipleConstrainedGenericFunctionWithOptionalParam<
    string,
    { size: number }
  >(input1, input2, arg1, arg2);
}

function checkMultipleConstrainedGenericFunctionWithOptionalParamObjectArray(
  input1: { length: number },
  input2: { size: number },
  arg1?: { length: number },
  arg2?: { size: number },
): [number | undefined, number | undefined] {
  return checkMultipleConstrainedGenericFunctionWithOptionalParam<
    { length: number },
    { size: number }
  >(input1, input2, arg1, arg2);
}

///////////////////////////////////////////////////////////////////////////////
// Builtin types
///////////////////////////////////////////////////////////////////////////////

function checkFieldOfString(s: string): boolean {
  return s.startsWith("foo");
}

function checkSubscriptionOf(): string {
  return (2024)["toString"]();
}
