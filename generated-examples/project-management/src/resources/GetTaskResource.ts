import type { Task_skip_id_, Task_skip_value_, Task } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetTaskResourceInputs extends SharedCollections {
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
}

export class GetTaskResource implements Resource<GetTaskResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetTaskResourceInputs,
    _context: Context,
  ): EagerCollection<Task_skip_id_, Task_skip_value_> {
    return inputs.tasks;
  }
}
