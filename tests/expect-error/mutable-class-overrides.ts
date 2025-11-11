// Example derived from docs/skjs_type_system.tex (Mutable class overrides).

// @ts-expect-error Out of bounds
class Base<E extends Event = Event> {
  handle(e: E): void {}
}

// @ts-expect-error Out of bounds
class Clicks extends Base<MouseEvent> {
  handle(e: MouseEvent): void {}
}

class SafeClicks extends Base {
  handle(e: Event) {
    if (e instanceof MouseEvent) {
      this.onClick(e);
    }
  }

  onClick(e: MouseEvent) {}
}
