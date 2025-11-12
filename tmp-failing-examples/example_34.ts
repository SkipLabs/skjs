// (1) Bivariance pitfall vs safe arrow functions
interface Service { call(x: { a: number } | { b: string }): void }
const bad: Service = { call(x: { a: number }) { x.a.toFixed() } }; // allowed (method bivariance)
// Prefer arrows (checked contravariantly):
type Fn = (x: { a: number } | { b: string }) => void;
const good: Fn = (x: { a: number }) => {}; // ERROR in strict TS (good!)

// (2) Express binding sanity
type Domain = (req: { params: { id: string } }) => Promise<{ id: string }>;
declare const toExpress: <P,Res,Body,Query,L>(h: any) => any;
declare const app: { get: (p: string, h: any) => void };
const d: Domain = async (r) => ({ id: r.params.id });
app.get("/u/:id", toExpress(d)); // OK

// (3) Koa context coherence
declare const requireUser: (h: (ctx: { user: { id: string } }) => Promise<void>) => any;
requireUser(async (ctx) => { ctx.user.id; }); // OK

// (4) Fastify hook refinement
declare const auth: (req: any, reply: any) => Promise<void>;
declare const f: { get: (p: string, o: { preHandler: typeof auth }, h: (req: any, reply: any) => any) => void };
f.get("/me", { preHandler: auth }, async (req, reply) => {
  const id = (req.user as { id: string }).id; // local refine after preHandler
  reply.send({ id });
});
