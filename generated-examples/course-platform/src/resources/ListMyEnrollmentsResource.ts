import type { User_skip_id_, Enrollment, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListMyEnrollmentsResourceInputs extends SharedCollections {
  readonly enrollmentsByUser: EagerCollection<User_skip_id_, Enrollment>;
}

export class ListMyEnrollmentsResource implements Resource<ListMyEnrollmentsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListMyEnrollmentsResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Enrollment> {
    return inputs.enrollmentsByUser;
  }
}
