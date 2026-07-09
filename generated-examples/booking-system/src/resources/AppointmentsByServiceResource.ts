import { AppointmentByServiceMapper } from "../mappers/AppointmentByServiceMapper.js";
import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  Service_skip_id_,
  Appointment,
  Service,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface AppointmentsByServiceResourceInputs extends SharedCollections {
  readonly appointments: EagerCollection<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
}

export class AppointmentsByServiceResource implements Resource<AppointmentsByServiceResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: AppointmentsByServiceResourceInputs,
    _context: Context,
  ): EagerCollection<Service_skip_id_, Appointment> {
    const appointmentsByService = inputs.appointments.map(
      AppointmentByServiceMapper,
    );
    return appointmentsByService;
  }
}
