import type {
  Appointment_skip_id_,
  Appointment_skip_value_,
  Appointment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetAppointmentResourceInputs extends SharedCollections {
  readonly appointments: EagerCollection<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
}

export class GetAppointmentResource implements Resource<GetAppointmentResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetAppointmentResourceInputs,
    _context: Context,
  ): EagerCollection<Appointment_skip_id_, Appointment_skip_value_> {
    return inputs.appointments;
  }
}
