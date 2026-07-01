import type { Widget_skip_id_, Widget_skip_value_, Widget } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetWidgetResourceInputs extends SharedCollections {
  readonly widgets: EagerCollection<Widget_skip_id_, Widget_skip_value_>;
}

export class GetWidgetResource implements Resource<GetWidgetResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetWidgetResourceInputs,
    _context: Context,
  ): EagerCollection<Widget_skip_id_, Widget_skip_value_> {
    return inputs.widgets;
  }
}
