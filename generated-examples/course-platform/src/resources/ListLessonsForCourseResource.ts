import type { Course_skip_id_, Lesson, Course } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListLessonsForCourseResourceInputs extends SharedCollections {
  readonly lessonsByCourse: EagerCollection<Course_skip_id_, Lesson>;
}

export class ListLessonsForCourseResource implements Resource<ListLessonsForCourseResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListLessonsForCourseResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, Lesson> {
    return inputs.lessonsByCourse;
  }
}
