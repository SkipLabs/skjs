// @skjs-callgraph
// fn:makeSpeak: method:Animal.speak
// fn:test: fn:makeSpeak
// method:Animal.speak: method:Dog.speak
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
