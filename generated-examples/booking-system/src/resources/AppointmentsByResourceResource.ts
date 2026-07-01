import { AppointmentsByResourceMapper } from "../mappers/AppointmentsByResourceMapper.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  BookableResource_skip_id_,
  Appointment,
  BookableResource,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface AppointmentsByResourceResourceInputs extends SharedCollections {
  readonly appointments: EagerCollection<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
}

export class AppointmentsByResourceResource implements Resource<AppointmentsByResourceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: AppointmentsByResourceResourceInputs,
    _context: Context,
  ): EagerCollection<BookableResource_skip_id_, Appointment> {
    return inputs.appointments.map(AppointmentsByResourceMapper);
  }
}
