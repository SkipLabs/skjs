import type { Course_skip_id_, Course_skip_value_, Course } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetCourseResourceInputs extends SharedCollections {
  readonly courses: EagerCollection<Course_skip_id_, Course_skip_value_>;
}

export class GetCourseResource implements Resource<GetCourseResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCourseResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, Course_skip_value_> {
    return inputs.courses;
  }
}
