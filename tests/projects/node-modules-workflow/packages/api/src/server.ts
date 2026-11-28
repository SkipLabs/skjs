import { createRoute } from "router-pkg";
import { verifyToken } from "router-pkg/middleware/auth";
// @skjs-expect-error Package subpath './internal' is not defined by 'exports' in 'router-pkg/package.json'
import { secretKey } from "router-pkg/internal";
import { formatLog } from "logger-pkg";
import { parseCount } from "untyped-lib";
import { validateId } from "@acme/schema";
import { apiVersion } from "versioned-pkg";

function handleRequest(token: string, rawCount: string, id: string): string {
  const route = createRoute("GET", "/items");
  const authed: boolean = verifyToken(token);
  const count: number = parseCount(rawCount);
  const valid: boolean = validateId(id);
  const ver: "v2" = apiVersion();
  const env: "dev" | "prod" = APP_ENV;
  if (authed && valid && count > 0) {
    return formatLog("info", `${route.method} ${route.path} ${ver} ${env}`);
  }
  return formatLog("warn", "denied");
}

function badVersion(): "v1" {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return apiVersion();
}

function badExcludedAmbient(): string {
  // @skjs-expect-error Cannot find name
  return IGNORED_GLOBAL;
}
