import type { Room_skip_id_, Room_skip_value_, Room } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetRoomResourceInputs extends SharedCollections {
  readonly rooms: EagerCollection<Room_skip_id_, Room_skip_value_>;
}

export class GetRoomResource implements Resource<GetRoomResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetRoomResourceInputs,
    _context: Context,
  ): EagerCollection<Room_skip_id_, Room_skip_value_> {
    return inputs.rooms;
  }
}
