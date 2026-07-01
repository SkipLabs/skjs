export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Appointment = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly cancelledBy?: string;
  readonly completedAt?: string;
  readonly createdAt: string;
  readonly customerId: string;
  readonly endsAt: string;
  readonly id: string;
  readonly notes?: string;
  readonly resourceId: string;
  readonly startsAt: string;
  readonly status: AppointmentStatus;
};

export type AppointmentList = {
  readonly items: Appointment[];
  readonly total?: number;
};

export type AppointmentList_skip_id_ = {
  readonly items: Appointment[];
  readonly total?: number;
};

export type AppointmentList_skip_value_ = {
  readonly items: Appointment[];
  readonly total?: number;
};

export type AppointmentStatus = "SCHEDULED" | "CANCELLED" | "COMPLETED";

export type AppointmentStatus_skip_id_ =
  | "SCHEDULED"
  | "CANCELLED"
  | "COMPLETED";

export type AppointmentStatus_skip_value_ =
  | "SCHEDULED"
  | "CANCELLED"
  | "COMPLETED";

export type Appointment_skip_id_ = string;

export type Appointment_skip_value_ = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly cancelledBy?: string;
  readonly completedAt?: string;
  readonly createdAt: string;
  readonly customerId: string;
  readonly endsAt: string;
  readonly notes?: string;
  readonly resourceId: string;
  readonly startsAt: string;
  readonly status: AppointmentStatus;
};

export type AvailabilityWindow = {
  readonly createdAt: string;
  readonly endsAt: string;
  readonly id: string;
  readonly resourceId: string;
  readonly startsAt: string;
};

export type AvailabilityWindowKey = {
  readonly id: string;
  readonly resourceId: string;
};

export type AvailabilityWindowList = { readonly items: AvailabilityWindow[] };

export type AvailabilityWindowList_skip_id_ = {
  readonly items: AvailabilityWindow[];
};

export type AvailabilityWindowList_skip_value_ = {
  readonly items: AvailabilityWindow[];
};

export type AvailabilityWindowStored = {
  readonly createdAt: string;
  readonly endsAt: string;
  readonly startsAt: string;
};

export type AvailabilityWindow_skip_id_ = {
  readonly id: string;
  readonly resourceId: string;
};

export type AvailabilityWindow_skip_value_ = {
  readonly createdAt: string;
  readonly endsAt: string;
  readonly startsAt: string;
};

export type BookableResource = {
  readonly createdAt: string;
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
};

export type BookableResource_skip_id_ = string;

export type BookableResource_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name: string;
  readonly ownerId: string;
};

export type CancelAppointmentRequest = { readonly cancellationReason?: string };

export type CancelAppointmentRequest_skip_id_ = {
  readonly cancellationReason?: string;
};

export type CancelAppointmentRequest_skip_value_ = {
  readonly cancellationReason?: string;
};

export type CreateAppointmentRequest = {
  readonly endsAt: string;
  readonly notes?: string;
  readonly resourceId: string;
  readonly startsAt: string;
};

export type CreateAppointmentRequest_skip_id_ = {
  readonly endsAt: string;
  readonly notes?: string;
  readonly resourceId: string;
  readonly startsAt: string;
};

export type CreateAppointmentRequest_skip_value_ = {
  readonly endsAt: string;
  readonly notes?: string;
  readonly resourceId: string;
  readonly startsAt: string;
};

export type CreateAvailabilityWindowRequest = {
  readonly endsAt: string;
  readonly startsAt: string;
};

export type CreateAvailabilityWindowRequest_skip_id_ = {
  readonly endsAt: string;
  readonly startsAt: string;
};

export type CreateAvailabilityWindowRequest_skip_value_ = {
  readonly endsAt: string;
  readonly startsAt: string;
};

export type CreateResourceRequest = {
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name: string;
};

export type CreateResourceRequest_skip_id_ = {
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name: string;
};

export type CreateResourceRequest_skip_value_ = {
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name: string;
};

export type GetAppointmentParams = { readonly appointmentId: string };

export type GetResourceParams = { readonly resourceId: string };

export type GetUserParams = { readonly userId: string };

export type ListAppointmentsParams = {
  readonly customerId?: string;
  readonly resourceId?: string;
  readonly status?: AppointmentStatus;
};

export type ListAvailabilityParams = { readonly resourceId: string };

export type ListResourcesParams = { readonly ownerId?: string };

export type RescheduleAppointmentRequest = {
  readonly endsAt: string;
  readonly notes?: string;
  readonly startsAt: string;
};

export type RescheduleAppointmentRequest_skip_id_ = {
  readonly endsAt: string;
  readonly notes?: string;
  readonly startsAt: string;
};

export type RescheduleAppointmentRequest_skip_value_ = {
  readonly endsAt: string;
  readonly notes?: string;
  readonly startsAt: string;
};

export type ResourceList = {
  readonly items: BookableResource[];
  readonly total?: number;
};

export type ResourceList_skip_id_ = {
  readonly items: BookableResource[];
  readonly total?: number;
};

export type ResourceList_skip_value_ = {
  readonly items: BookableResource[];
  readonly total?: number;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateResourceRequest = {
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name?: string;
};

export type UpdateResourceRequest_skip_id_ = {
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name?: string;
};

export type UpdateResourceRequest_skip_value_ = {
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name?: string;
};

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
};
