import type { LessonKey, Lesson_skip_value_, Lesson } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetLessonByIdResourceInputs extends SharedCollections {
  readonly lessons: EagerCollection<LessonKey, Lesson_skip_value_>;
}

export class GetLessonByIdResource implements Resource<GetLessonByIdResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetLessonByIdResourceInputs,
    _context: Context,
  ): EagerCollection<LessonKey, Lesson_skip_value_> {
    return inputs.lessons;
  }
}
