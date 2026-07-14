// Test class inheritance with different constructor signatures

class BaseClass {
  name: string;

  constructor(name: string) {
    this.name = name;
  }

  getName(): string {
    return this.name;
  }
}

class DerivedClassWithDifferentConstructor extends BaseClass {
  age: number;
  email: string;

  // Constructor with different signature than base class
  constructor(name: string, age: number, email: string) {
    super(name);
    this.age = age;
    this.email = email;
  }

  getAge(): number {
    return this.age;
  }

  getEmail(): string {
    return this.email;
  }

  getFullInfo(): string {
    return `${this.getName()} (${this.age}) - ${this.email}`;
  }
}

class AnotherDerivedClass extends BaseClass {
  id: number;

  // Another different constructor signature
  constructor(id: number, name: string) {
    super(name);
    this.id = id;
  }

  getId(): number {
    return this.id;
  }

  getInfo(): string {
    return `ID: ${this.id}, Name: ${this.getName()}`;
  }
}

// Test the inheritance functionality
function testClassInheritance(): void {
  const base = new BaseClass("John");
  const derived1 = new DerivedClassWithDifferentConstructor(
    "Alice",
    30,
    "alice@example.com",
  );
  const derived2 = new AnotherDerivedClass(123, "Bob");

  console.log("Base class:", base.getName());
  console.log("Derived class 1:", derived1.getFullInfo());
  console.log("Derived class 2:", derived2.getInfo());

  // Test that inheritance works properly
  console.log("derived1 instanceof BaseClass:", derived1 instanceof BaseClass);
  console.log("derived2 instanceof BaseClass:", derived2 instanceof BaseClass);
}

testClassInheritance();
