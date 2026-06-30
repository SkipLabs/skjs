import type { Course_skip_id_, Course_skip_value_, Course } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetCourseByIdResourceInputs extends SharedCollections {
  readonly courses: EagerCollection<Course_skip_id_, Course_skip_value_>;
}

export class GetCourseByIdResource implements Resource<GetCourseByIdResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetCourseByIdResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, Course_skip_value_> {
    return inputs.courses;
  }
}
