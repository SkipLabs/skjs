import { Child } from "./child";

export function useChild(): number {
  return new Child().method();
}
