// Examples demonstrating successful constructor signature types (`new`) functionality

// Simple non-generic class
class Person {
  name: string;
  age: number;

  constructor(name: string, age: number) {
    this.name = name;
    this.age = age;
  }

  greet(): string {
    return `Hello, I'm ${this.name} and I'm ${this.age} years old.`;
  }
}

// Basic constructor assignment with non-generic class
function demonstrateBasicAssignment(): void {
  const PersonCtor: typeof Person = Person;

  const person = new PersonCtor("Alice", 30);

  console.log(person.greet());
}

// Multiple constructor parameters
class Point {
  x: number;
  y: number;

  constructor(x: number, y: number) {
    this.x = x;
    this.y = y;
  }
}

// Constructor signature with multiple parameters
function createPoint(
  PointConstructor: new (x: number, y: number) => Point,
): Point {
  return new PointConstructor(10, 20);
}

function demonstrateMultipleParams(): void {
  const point = createPoint(Point);
  console.log(`Point: (${point.x}, ${point.y})`); // Point: (10, 20)
}

// Array of constructor functions
class Animal {
  name: string;
  constructor(name: string) {
    this.name = name;
  }
}

class Dog extends Animal {
  constructor(name: string) {
    super(name);
  }
}

class Cat extends Animal {
  constructor(name: string) {
    super(name);
  }
}

function demonstrateConstructorArray(): void {
  const animals: Array<Animal> = new Array<Animal>();

  // Demonstrate different constructors
  animals.push(new Dog("Rex"));
  animals.push(new Cat("Whiskers"));

  console.log(animals.map((animal) => animal.name)); // ["Rex", "Whiskers"]
}

// Constructor with no parameters (non-generic)
class SimpleLogger {
  constructor() {}

  log(message: string): void {
    console.log(`[LOG] ${message}`);
  }
}

function createSimpleLogger(
  LoggerConstructor: new () => SimpleLogger,
): SimpleLogger {
  return new LoggerConstructor();
}

function demonstrateNoParams(): void {
  const logger = createSimpleLogger(SimpleLogger);
  logger.log("Constructor signature types working!");
}

// Generic class example with constructor signatures
class Container<T> {
  value: T;

  constructor(value: T) {
    this.value = value;
  }

  getValue(): T {
    return this.value;
  }
}

function createContainer<T>(
  ContainerConstructor: new (value: T) => Container<T>,
  value: T,
): Container<T> {
  return new ContainerConstructor(value);
}

function demonstrateGenericClass(): void {
  // Direct assignment of generic constructor signature with explicit types
  const ContainerCtor: new <T>(value: T) => Container<T> = Container;

  // Create containers using the constructor signature variables
  const stringContainer = new ContainerCtor("hello world");
  const numberContainer = new ContainerCtor(42);

  console.log(`String container: ${stringContainer.getValue()}`);
  console.log(`Number container: ${numberContainer.getValue()}`);

  // Direct instantiation also works
  const directContainer = new Container("direct creation");
}

// Constructor signature for specific types
function createPointFromConstructor(
  ctor: new (x: number, y: number) => Point,
): Point {
  return new ctor(5, 10);
}

function createPersonFromConstructor(
  ctor: new (name: string, age: number) => Person,
  name: string,
  age: number,
): Person {
  return new ctor(name, age);
}

function demonstrateSpecificConstructors(): void {
  const point = createPointFromConstructor(Point);
  const person = createPersonFromConstructor(Person, "Bob", 25);

  console.log(`Point: (${point.x}, ${point.y})`);
  console.log(person.greet());
}

// Main demonstration function
function main(): void {
  demonstrateBasicAssignment();
  demonstrateMultipleParams();
  demonstrateConstructorArray();
  demonstrateNoParams();
  demonstrateGenericClass();
  demonstrateSpecificConstructors();
}

main();
