import {
  defaultParamEncoder,
  PolledHTTPResource,
  PolledExternalService,
  SkipExternalService,
  fetchJSON,
  Sum,
  Min,
  Max,
  Count,
  Entrypoint,
} from "@skipruntime/helpers";
import { Json } from "@skipruntime/core";

const s: string = defaultParamEncoder({ a: 1 });

const resources: { [resource: string]: PolledHTTPResource } = {
  r: {
    url: "http://example.com",
    interval: 1000,
    conv: (data: Json) => [],
  },
};
const polled = new PolledExternalService(resources);

const remote = new SkipExternalService("url", "control_url");
const remote2 = SkipExternalService.direct({
  host: "h",
  streaming_port: 1,
  control_port: 2,
});

async function useFetch(): Promise<void> {
  const [v, headers] = await fetchJSON<Json>("http://example.com");
}

const sum = new Sum();
const min = new Min();
const max = new Max();
const count = new Count<Json>();

const ep: Entrypoint = { host: "h", streaming_port: 1, control_port: 2 };
