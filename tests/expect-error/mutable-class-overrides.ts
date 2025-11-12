// Example derived from docs/skjs_type_system.tex (Mutable class overrides).

declare class Event {}
declare class MouseEvent extends Event {}

// @ts-expect-error Optional type parameters are not supported for classes
class Base<E extends Event = Event> {
  handle(e: E): void {}
}

class Clicks extends Base<MouseEvent> {
  handle(e: MouseEvent): void {}
}

// @ts-expect-error Invalid number of type arguments
class SafeClicks extends Base {
  handle(e: Event): void {
    if (e instanceof MouseEvent) {
      this.onClick(e);
    }
  }

  onClick(e: MouseEvent): void {}
}

class SafeClicks2 extends Base<Event> {
  handle(e: Event): void {
    if (e instanceof MouseEvent) {
      this.onClick(e);
    }
  }

  onClick(e: MouseEvent): void {}
}
