import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type CountAccum = number;

export type Course = {
  readonly createdAt: string;
  readonly description?: string;
  readonly enrollmentCount?: number;
  readonly id: string;
  readonly instructorId: string;
  readonly lessonCount?: number;
  readonly published: boolean;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type CourseList = { readonly courses: Course[] } & {
  readonly [key: string]: Json | null;
};

export type CourseList_skip_id_ = { readonly courses: Course[] } & {
  readonly [key: string]: Json | null;
};

export type CourseList_skip_value_ = { readonly courses: Course[] } & {
  readonly [key: string]: Json | null;
};

export type CourseStored = {
  readonly createdAt: string;
  readonly description?: string;
  readonly instructorId: string;
  readonly published: boolean;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type Course_skip_id_ = string;

export type Course_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly enrollmentCount?: number;
  readonly instructorId: string;
  readonly lessonCount?: number;
  readonly published: boolean;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type CreateCourseRequest = {
  readonly description?: string;
  readonly published?: boolean;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateCourseRequest_skip_id_ = {
  readonly description?: string;
  readonly published?: boolean;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateCourseRequest_skip_value_ = {
  readonly description?: string;
  readonly published?: boolean;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateLessonRequest = {
  readonly content?: string;
  readonly durationMinutes?: number;
  readonly orderIndex: number;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateLessonRequest_skip_id_ = {
  readonly content?: string;
  readonly durationMinutes?: number;
  readonly orderIndex: number;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type CreateLessonRequest_skip_value_ = {
  readonly content?: string;
  readonly durationMinutes?: number;
  readonly orderIndex: number;
  readonly title: string;
} & { readonly [key: string]: Json | null };

export type Enrollment = {
  readonly courseId: string;
  readonly enrolledAt: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type EnrollmentKey = {
  readonly courseId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type EnrollmentList = { readonly enrollments: Enrollment[] } & {
  readonly [key: string]: Json | null;
};

export type EnrollmentList_skip_id_ = { readonly enrollments: Enrollment[] } & {
  readonly [key: string]: Json | null;
};

export type EnrollmentList_skip_value_ = {
  readonly enrollments: Enrollment[];
} & { readonly [key: string]: Json | null };

export type Enrollment_skip_id_ = {
  readonly courseId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type Enrollment_skip_value_ = { readonly enrolledAt: string } & {
  readonly [key: string]: Json | null;
};

export type GetCourseParams = { readonly courseId: string } & {
  readonly [key: string]: Json | null;
};

export type GetEnrollmentParams = {
  readonly courseId: string;
  readonly userIdParam: string;
} & { readonly [key: string]: Json | null };

export type GetLessonParams = { readonly lessonId: string } & {
  readonly [key: string]: Json | null;
};

export type GetUserParams = { readonly userIdParam: string } & {
  readonly [key: string]: Json | null;
};

export type Lesson = {
  readonly content?: string;
  readonly courseId: string;
  readonly createdAt: string;
  readonly durationMinutes?: number;
  readonly id: string;
  readonly orderIndex: number;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type LessonList = { readonly lessons: Lesson[] } & {
  readonly [key: string]: Json | null;
};

export type LessonList_skip_id_ = { readonly lessons: Lesson[] } & {
  readonly [key: string]: Json | null;
};

export type LessonList_skip_value_ = { readonly lessons: Lesson[] } & {
  readonly [key: string]: Json | null;
};

export type Lesson_skip_id_ = string;

export type Lesson_skip_value_ = {
  readonly content?: string;
  readonly courseId: string;
  readonly createdAt: string;
  readonly durationMinutes?: number;
  readonly orderIndex: number;
  readonly title: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type ListCoursesParams = {
  readonly instructorId?: string;
  readonly published?: boolean;
} & { readonly [key: string]: Json | null };

export type UpdateCourseRequest = {
  readonly description?: string;
  readonly published?: boolean;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCourseRequest_skip_id_ = {
  readonly description?: string;
  readonly published?: boolean;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCourseRequest_skip_value_ = {
  readonly description?: string;
  readonly published?: boolean;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateLessonRequest = {
  readonly content?: string;
  readonly durationMinutes?: number;
  readonly orderIndex?: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateLessonRequest_skip_id_ = {
  readonly content?: string;
  readonly durationMinutes?: number;
  readonly orderIndex?: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateLessonRequest_skip_value_ = {
  readonly content?: string;
  readonly durationMinutes?: number;
  readonly orderIndex?: number;
  readonly title?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
