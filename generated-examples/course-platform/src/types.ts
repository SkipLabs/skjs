export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Course = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly instructorId: string;
  readonly publishedAt?: string;
  readonly status: CourseStatus;
  readonly title: string;
  readonly updatedAt: string;
};

export type CoursePage = { readonly items: Course[]; readonly total: number };

export type CoursePage_skip_id_ = {
  readonly items: Course[];
  readonly total: number;
};

export type CoursePage_skip_value_ = {
  readonly items: Course[];
  readonly total: number;
};

export type CourseStatus = "DRAFT" | "PUBLISHED";

export type CourseStatus_skip_id_ = "DRAFT" | "PUBLISHED";

export type CourseStatus_skip_value_ = "DRAFT" | "PUBLISHED";

export type Course_skip_id_ = string;

export type Course_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly instructorId: string;
  readonly publishedAt?: string;
  readonly status: CourseStatus;
  readonly title: string;
  readonly updatedAt: string;
};

export type CreateCourseRequest = {
  readonly description?: string;
  readonly title: string;
};

export type CreateCourseRequest_skip_id_ = {
  readonly description?: string;
  readonly title: string;
};

export type CreateCourseRequest_skip_value_ = {
  readonly description?: string;
  readonly title: string;
};

export type CreateLessonRequest = {
  readonly content?: string;
  readonly position: number;
  readonly title: string;
};

export type CreateLessonRequest_skip_id_ = {
  readonly content?: string;
  readonly position: number;
  readonly title: string;
};

export type CreateLessonRequest_skip_value_ = {
  readonly content?: string;
  readonly position: number;
  readonly title: string;
};

export type Enrollment = {
  readonly completedAt?: string;
  readonly courseId: string;
  readonly enrolledAt: string;
  readonly progressPercent: number;
  readonly status: EnrollmentStatus;
  readonly userId: string;
};

export type EnrollmentByCourseValue = {
  readonly completedAt?: string;
  readonly courseId: string;
  readonly enrolledAt: string;
  readonly progressPercent: number;
  readonly status: "ACTIVE" | "COMPLETED";
  readonly userId: string;
};

export type EnrollmentByUserValue = {
  readonly completedAt?: string;
  readonly courseId: string;
  readonly enrolledAt: string;
  readonly progressPercent: number;
  readonly status: "ACTIVE" | "COMPLETED";
  readonly userId: string;
};

export type EnrollmentKey = {
  readonly courseId: string;
  readonly userId: string;
};

export type EnrollmentPage = {
  readonly items: Enrollment[];
  readonly total: number;
};

export type EnrollmentPage_skip_id_ = {
  readonly items: Enrollment[];
  readonly total: number;
};

export type EnrollmentPage_skip_value_ = {
  readonly items: Enrollment[];
  readonly total: number;
};

export type EnrollmentStatus = "ACTIVE" | "COMPLETED";

export type EnrollmentStatus_skip_id_ = "ACTIVE" | "COMPLETED";

export type EnrollmentStatus_skip_value_ = "ACTIVE" | "COMPLETED";

export type Enrollment_skip_id_ = {
  readonly courseId: string;
  readonly userId: string;
};

export type Enrollment_skip_value_ = {
  readonly completedAt?: string;
  readonly enrolledAt: string;
  readonly progressPercent: number;
  readonly status: EnrollmentStatus;
};

export type GetCourseByIdParams = { readonly courseId: string };

export type GetEnrollmentParams = {
  readonly courseId: string;
  readonly enrolleeUserId: string;
};

export type GetLessonByIdParams = {
  readonly courseId: string;
  readonly lessonId: string;
};

export type GetUserByIdParams = { readonly userId: string };

export type Lesson = {
  readonly content?: string;
  readonly courseId: string;
  readonly createdAt: string;
  readonly id: string;
  readonly position: number;
  readonly title: string;
  readonly updatedAt: string;
};

export type LessonByCourseValue = {
  readonly content?: string;
  readonly courseId: string;
  readonly createdAt: string;
  readonly id: string;
  readonly position: number;
  readonly title: string;
  readonly updatedAt: string;
};

export type LessonKey = { readonly courseId: string; readonly id: string };

export type LessonPage = { readonly items: Lesson[]; readonly total: number };

export type LessonPage_skip_id_ = {
  readonly items: Lesson[];
  readonly total: number;
};

export type LessonPage_skip_value_ = {
  readonly items: Lesson[];
  readonly total: number;
};

export type Lesson_skip_id_ = {
  readonly courseId: string;
  readonly id: string;
};

export type Lesson_skip_value_ = {
  readonly content?: string;
  readonly createdAt: string;
  readonly position: number;
  readonly title: string;
  readonly updatedAt: string;
};

export type ListCoursesParams = {
  readonly instructorId?: string;
  readonly published?: boolean;
};

export type ListEnrollmentsForCourseParams = { readonly courseId: string };

export type ListLessonsForCourseParams = { readonly courseId: string };

export type ListMyEnrollmentsParams = {
  readonly status?: "ACTIVE" | "COMPLETED";
  readonly userId: string;
};

export type UpdateCourseRequest = {
  readonly description?: string;
  readonly status?: CourseStatus;
  readonly title?: string;
};

export type UpdateCourseRequest_skip_id_ = {
  readonly description?: string;
  readonly status?: CourseStatus;
  readonly title?: string;
};

export type UpdateCourseRequest_skip_value_ = {
  readonly description?: string;
  readonly status?: CourseStatus;
  readonly title?: string;
};

export type UpdateEnrollmentRequest = {
  readonly progressPercent?: number;
  readonly status?: EnrollmentStatus;
};

export type UpdateEnrollmentRequest_skip_id_ = {
  readonly progressPercent?: number;
  readonly status?: EnrollmentStatus;
};

export type UpdateEnrollmentRequest_skip_value_ = {
  readonly progressPercent?: number;
  readonly status?: EnrollmentStatus;
};

export type UpdateLessonRequest = {
  readonly content?: string;
  readonly position?: number;
  readonly title?: string;
};

export type UpdateLessonRequest_skip_id_ = {
  readonly content?: string;
  readonly position?: number;
  readonly title?: string;
};

export type UpdateLessonRequest_skip_value_ = {
  readonly content?: string;
  readonly position?: number;
  readonly title?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
};
