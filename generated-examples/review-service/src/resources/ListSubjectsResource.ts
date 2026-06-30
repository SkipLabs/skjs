import type {
  Subject_skip_id_,
  Subject_skip_value_,
  Subject,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListSubjectsResourceInputs extends SharedCollections {
  readonly subjects: EagerCollection<Subject_skip_id_, Subject_skip_value_>;
}

export class ListSubjectsResource implements Resource<ListSubjectsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListSubjectsResourceInputs,
    _context: Context,
  ): EagerCollection<Subject_skip_id_, Subject_skip_value_> {
    return inputs.subjects;
  }
}
