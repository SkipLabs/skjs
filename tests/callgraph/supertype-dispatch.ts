// @skjs-callgraph
// fn:makeSpeak: method:Animal.speak
// fn:test: fn:makeSpeak
//
// Missing edge: fn:makeSpeak should also depend on method:Dog.speak, since
// a.speak() can dispatch to Dog's override at runtime. Currently only
// method:Animal.speak is recorded because a is typed as Animal.
interface Animal {
  speak(): string;
}
class Dog implements Animal {
  speak(): string {
    return "woof";
  }
}
function makeSpeak(a: Animal): string {
  return a.speak();
}
function test(): string {
  return makeSpeak(new Dog());
}
