import type { Course_skip_id_, Enrollment, Course } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListEnrollmentsForCourseResourceInputs extends SharedCollections {
  readonly enrollmentsByCourse: EagerCollection<Course_skip_id_, Enrollment>;
}

export class ListEnrollmentsForCourseResource implements Resource<ListEnrollmentsForCourseResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListEnrollmentsForCourseResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, Enrollment> {
    return inputs.enrollmentsByCourse;
  }
}
