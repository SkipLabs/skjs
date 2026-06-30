import type { Task_skip_id_, Task_skip_value_, Task } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetTaskStoredResourceInputs extends SharedCollections {
  readonly tasks: EagerCollection<Task_skip_id_, Task_skip_value_>;
}

export class GetTaskStoredResource implements Resource<GetTaskStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetTaskStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Task_skip_id_, Task_skip_value_> {
    return inputs.tasks;
  }
}
