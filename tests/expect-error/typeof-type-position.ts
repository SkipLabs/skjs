///////////////////////////////////////////////////////////////////////////////
// Tests for typeof type operator (type position)
// type T = typeof expression
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// typeof undefined - different contexts
///////////////////////////////////////////////////////////////////////////////

// In type alias
type UndefinedType = typeof undefined;

// In function return type
function testTypeofUndefinedReturn(): typeof undefined {
  return undefined;
}

// In function parameter type
function testTypeofUndefinedParam(x: typeof undefined): void {}

// In union at top level
type MaybeNumber = number | typeof undefined;

// In function parameter with union
function testTypeofUndefinedUnion(x: number | typeof undefined): number {
  if (x === undefined) {
    return 0;
  }
  return x;
}

// Inside function - local variable annotation
function testTypeofUndefinedLocal(): void {
  const x: typeof undefined = undefined;
}

///////////////////////////////////////////////////////////////////////////////
// typeof class names (constructor signatures) - different contexts
///////////////////////////////////////////////////////////////////////////////

class Point {
  x: number;
  y: number;
  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }
}

// In type alias
type PointConstructor = typeof Point;

// In function parameter
function usePointConstructorParam(Ctor: typeof Point): Point {
  return new Ctor(1, 2);
}

// In function return type (returning constructor)
function getPointConstructor(): typeof Point {
  return Point;
}

// Inside function - local variable annotation
function testTypeofClassLocal(): void {
  const Ctor: typeof Point = Point;
  const p: Point = new Ctor(1, 2);
}

// Class with no explicit constructor
class Simple {
  value: number = 0;
}

type SimpleConstructor = typeof Simple;
function useSimpleConstructor(Ctor: SimpleConstructor): Simple {
  return new Ctor();
}

// Class extending another class
class Point3D extends Point {
  z: number;
  constructor(x: number, y: number, z: number) {
    super(x, y);
    this.z = z;
  }
}

type Point3DConstructor = typeof Point3D;
function usePoint3DConstructor(Ctor: Point3DConstructor): Point3D {
  return new Ctor(1, 2, 3);
}

///////////////////////////////////////////////////////////////////////////////
// typeof class - factory pattern
///////////////////////////////////////////////////////////////////////////////

function factoryPattern(Ctor: typeof Point, x: number, y: number): Point {
  return new Ctor(x, y);
}

function testInstanceVsConstructor(p: Point, Ctor: typeof Point): Point {
  return new Ctor(p.x, p.y);
}

///////////////////////////////////////////////////////////////////////////////
// typeof class with static members
///////////////////////////////////////////////////////////////////////////////

class WithStatic {
  static readonly DEFAULT: number = 42;
  value: number;
  constructor(value: number) {
    this.value = value;
  }
}

// FIXME: Constructor type should include static members
type WithStaticConstructor = typeof WithStatic;
function accessStaticThroughTypeof(Ctor: WithStaticConstructor): number {
  // @skjs-expect-error Invalid return type
  return Ctor.DEFAULT;
}

///////////////////////////////////////////////////////////////////////////////
// typeof class - negative tests
///////////////////////////////////////////////////////////////////////////////

// Wrong argument count
function wrongArgCount(Ctor: typeof Point): Point {
  // @skjs-expect-error Invalid call
  return new Ctor(1);
}

// Wrong argument type
function wrongArgType(Ctor: typeof Point): Point {
  // @skjs-expect-error Invalid call
  return new Ctor("a", "b");
}

///////////////////////////////////////////////////////////////////////////////
// typeof with top-level variables
///////////////////////////////////////////////////////////////////////////////

// number variable - type alias context
const myNumber: number = 42;
type MyNumberType = typeof myNumber;

// string variable - in function parameter
const myString: string = "hello";
function testStringParam(x: typeof myString): string {
  return x;
}

// boolean variable - in function return type
const myBool: boolean = true;
function testBoolReturn(): typeof myBool {
  return true;
}

// variable typeof inside function - local variable annotation
function testTypeofVarLocal(): void {
  const num: number = 42;
  // Inside function, typeof variable should also work once implemented
  // For now, this would error if we tried to use it
}

///////////////////////////////////////////////////////////////////////////////
// FIXME: Generic classes with typeof not yet supported
///////////////////////////////////////////////////////////////////////////////

class Container<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
}

// @skjs-expect-error Invalid number of type arguments
type ContainerConstructor = typeof Container;

///////////////////////////////////////////////////////////////////////////////
// typeof with function names
///////////////////////////////////////////////////////////////////////////////

// Simple function
function myFunc(x: number): string {
  return x.toString();
}

type MyFuncType = typeof myFunc;

// Function with multiple parameters
function multiParam(a: number, b: string, c: boolean): number {
  return a;
}

type MultiParamType = typeof multiParam;

// Function returning void
function voidFunc(): void {}

type VoidFuncType = typeof voidFunc;

// typeof function in parameter position
function useFuncType(f: typeof myFunc): string {
  return f(42);
}

// typeof function in return position
function returnFuncType(): typeof myFunc {
  return myFunc;
}

///////////////////////////////////////////////////////////////////////////////
// typeof for property access - static class members
///////////////////////////////////////////////////////////////////////////////

class AppConfig {
  static readonly DEFAULT_PORT: number = 8080;
  static readonly DEFAULT_HOST: string = "localhost";
  instanceField: number = 0;
}

// Static member in type alias context (no TCEnv)
// @skjs-expect-error TODO: typeof for complex expressions
type DefaultPortType = typeof AppConfig.DEFAULT_PORT;

// Static member in function parameter (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function useDefaultPort(p: typeof AppConfig.DEFAULT_PORT): number {
  return p;
}

// Static member in function return type (TCEnv available)
// @skjs-expect-error TODO: typeof for complex expressions
function getDefaultHost(): typeof AppConfig.DEFAULT_HOST {
  return "localhost";
}

///////////////////////////////////////////////////////////////////////////////
// prototype access - explicitly not supported
///////////////////////////////////////////////////////////////////////////////

class Config {
  port: number = 3000;
  host: string = "localhost";
}

// @skjs-expect-error TODO: typeof for complex expressions
type PortType = typeof Config.prototype.port;
