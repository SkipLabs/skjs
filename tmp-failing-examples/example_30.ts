import type { Request, Response, NextFunction, RequestHandler } from "express";

// Accept a precise, domain-level handler and adapt it to Express's RequestHandler.
export function toExpress<P, ResBody, ReqBody, ReqQuery, Locals extends Record<string, any> = {}>(
  h: (req: Request<P, ResBody, ReqBody, ReqQuery, Locals>) => Promise<ResBody>
): RequestHandler<P, ResBody, ReqBody, ReqQuery, Locals> {
  return (req, res, next) => {
    h(req).then((body) => { res.json(body as ResBody); }, next);
  };
}

// Usage (no bivariance needed):
type User = { id: string; email: string };
const getMe = async (req: Request<{id: string}, User, unknown, unknown>) => ({ id: req.params.id, email: "x@y" });
app.get("/users/:id", toExpress(getMe));
