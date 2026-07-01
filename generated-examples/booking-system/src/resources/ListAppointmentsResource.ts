import { FilterAppointmentsMapper } from "../mappers/FilterAppointmentsMapper.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  AppointmentStatus,
  ListAppointmentsParams,
  Appointment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListAppointmentsResourceInputs extends SharedCollections {
  readonly appointments: EagerCollection<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
}

export class ListAppointmentsResource implements Resource<ListAppointmentsResourceInputs> {
  private readonly customerId: string | null;
  private readonly resourceId: string | null;
  private readonly status: AppointmentStatus | null;

  constructor(params: ListAppointmentsParams) {
    this.customerId = params.customerId ?? null;
    this.resourceId = params.resourceId ?? null;
    this.status = params.status ?? null;
  }

  instantiate(
    inputs: ListAppointmentsResourceInputs,
    _context: Context,
  ): EagerCollection<Appointment_skip_id_, Appointment_skip_value_> {
    return inputs.appointments.map(
      FilterAppointmentsMapper,
      this.customerId,
      this.resourceId,
      this.status,
    );
  }
}
