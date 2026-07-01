import type { Room_skip_id_, Room_skip_value_, Room } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListRoomsResourceInputs extends SharedCollections {
  readonly rooms: EagerCollection<Room_skip_id_, Room_skip_value_>;
}

export class ListRoomsResource implements Resource<ListRoomsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListRoomsResourceInputs,
    _context: Context,
  ): EagerCollection<Room_skip_id_, Room_skip_value_> {
    return inputs.rooms;
  }
}
