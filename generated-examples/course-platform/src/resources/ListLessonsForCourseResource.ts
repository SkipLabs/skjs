import { LessonsByCourseMapper } from "../mappers/LessonsByCourseMapper.js";
import type {
  LessonKey,
  Lesson_skip_value_,
  Course_skip_id_,
  LessonByCourseValue,
  Lesson,
  Course,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListLessonsForCourseResourceInputs extends SharedCollections {
  readonly lessons: EagerCollection<LessonKey, Lesson_skip_value_>;
}

export class ListLessonsForCourseResource implements Resource<ListLessonsForCourseResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListLessonsForCourseResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, LessonByCourseValue> {
    const lessonsByCourse = inputs.lessons.map(LessonsByCourseMapper);
    return lessonsByCourse;
  }
}
