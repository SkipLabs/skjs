import { tag } from "foo";
import { sharedVal } from "shared";

function useFromB(): ["root", number] {
  return [tag(), sharedVal()];
}
