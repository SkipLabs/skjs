import { apiVersion } from "versioned-pkg";
import { formatLog } from "logger-pkg";

function workerInfo(): ["v1", string, "dev" | "prod"] {
  return [apiVersion(), formatLog("info", "ready"), APP_ENV];
}

function badLogLevel(): string {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  return formatLog("debug", "bad");
}
