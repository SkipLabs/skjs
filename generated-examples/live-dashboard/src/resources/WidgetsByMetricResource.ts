import { WidgetByMetricMapper } from "../mappers/WidgetByMetricMapper.js";
import type {
  Widget_skip_id_,
  Widget_skip_value_,
  Metric_skip_id_,
  Widget,
  Metric,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface WidgetsByMetricResourceInputs extends SharedCollections {
  readonly widgets: EagerCollection<Widget_skip_id_, Widget_skip_value_>;
}

export class WidgetsByMetricResource implements Resource<WidgetsByMetricResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: WidgetsByMetricResourceInputs,
    _context: Context,
  ): EagerCollection<Metric_skip_id_, Widget> {
    const widgetsByMetric = inputs.widgets.map(WidgetByMetricMapper);
    return widgetsByMetric;
  }
}
