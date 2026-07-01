import type { Course_skip_id_, CourseStored, Course } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetCourseStoredResourceInputs extends SharedCollections {
  readonly coursesStored: EagerCollection<Course_skip_id_, CourseStored>;
}

export class GetCourseStoredResource implements Resource<GetCourseStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCourseStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, CourseStored> {
    return inputs.coursesStored;
  }
}
