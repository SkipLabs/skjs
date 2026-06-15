// A class cannot extend an interface: an interface has no runtime value to use
// as a superclass (tsc TS2689). Interfaces may still extend interfaces or
// classes, and a class may extend a name merged with a constructable value.

interface IBase {
  a: number;
}

class CBase {
  a: number = 1;
}

// @ts-expect-error Cannot extend an interface 'IBase'. Did you mean 'implements'?
class ClassExtendsInterface extends IBase {
  b: number = 2;
}

// @ts-expect-error Cannot extend an interface 'IBase'. Did you mean 'implements'?
abstract class AbstractExtendsInterface extends IBase {
  b: number = 2;
}

// Interfaces may extend interfaces.
interface InterfaceExtendsInterface extends IBase {
  b: number;
}

// Interfaces may extend classes.
interface InterfaceExtendsClass extends CBase {
  b: number;
}

// A class may extend a name merged with a constructable value declaration: the
// value provides the runtime constructor.
interface Merged {
  a: number;
}
declare const Merged: { new (): { a: number } };
class ClassExtendsMerged extends Merged {
  b: number = 2;
}
