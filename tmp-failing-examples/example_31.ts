import type Koa from "koa";

// 1) Augment DefaultContext once, in one module (declaration merging).
declare module "koa" {
  interface DefaultContext {
    user?: { id: string; role: "admin" | "user" };
  }
}

// 2) Adapter: accept a narrower ctx (with guaranteed 'user') and expose a broad Koa Middleware.
type AuthedCtx = Koa.ParameterizedContext<Koa.DefaultState, Koa.DefaultContext & { user: { id: string; role: "admin" | "user" } }>;

export const requireUser =
  (h: (ctx: AuthedCtx) => Promise<void>): Koa.Middleware =>
  async (ctx, next) => {
    if (!ctx.user) ctx.throw(401);
    await h(ctx as AuthedCtx);   // single, local cast after runtime guard
    return next();
  };

// Usage:
app.use(requireUser(async (ctx) => {
  ctx.body = { hello: ctx.user.id };
}));
