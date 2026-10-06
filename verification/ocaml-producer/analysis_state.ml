(* One inference pass owns its candidate output, lexical metadata and active
   typing scope. The diagnostic observations belong to the enclosing run. *)
open Semantic
open Environment
open Source
open Type_queries
open Proposal_types
type env = (string * Environment.binding) list
type expression_infer = ?expected:ty -> env -> Source.expr -> ty
type body_infer = Json.t -> ty option -> ty list ref -> env -> Source.stmt list -> env

type t = {
  diagnostics: Proposal_diagnostics.state;
  flows: Flow.graph list;
  offered: (Json.t * Semantic.signature list) list;
  declarations: Source.declaration list;
  module_functions: (string * ty Lazy.t) list;
  f: Source.fn;
  assumed: (Json.t * ty) list;
  env0: env;
  rigid_bounds: (Semantic.rigid * ty) list ref;
  writes: (Json.t * ty) list ref;
  entries: entry list ref;
  expressions: expression list ref;
  instantiations: ((string * Json.t) * (string * type_argument) list) list ref;
  current_point: string ref;
  contracts: contract list ref;
  typing_roots: (string * Execution.plan * env) list ref;
  executions: (string * Json.t, Execution.plan) Hashtbl.t;
  expression_hints: (Json.t, Source.expr) Hashtbl.t;
  evolving: (string * (Json.t * bool)) list ref;
  grown_locals: string list ref;
  exact_locals: string list ref;
  closures: (string * (Json.t * ty list)) list ref;
  requests: (Json.t * Semantic.signature) list ref;
  classes: (string * (Json.t * ty list * ty * (Semantic.key * string) list)) list ref;
  fresh_constructor: bool ref;
  objects: (string * (Semantic.key * Source.expr) list) list ref;
  exact_allocs: Json.t list ref;
  instances: ((string * Json.t) * ty) list ref;
  arrows: (Json.t * overlay list) list ref;
  speculative_typing: bool ref;
  block_result: ty option ref;
  block_returned: ty list ref ref;
  following: (Json.t, Source.stmt list) Hashtbl.t;
}

let create diagnostics flows offered declarations module_functions bounds assumed (f:Source.fn) =
  let executions = Hashtbl.create 128 and expression_hints = Hashtbl.create 128 in
  List.iter (fun (graph:Flow.graph) -> Array.iter (fun (node:Flow.node) ->
    List.iter (fun (source,plan) -> Hashtbl.replace executions (node.Flow.point,source) plan)
      node.Flow.executions) graph.Flow.nodes) flows;
  let rec register_expression (e:Source.expr) =
    Hashtbl.replace expression_hints e.pos e;
    (match e.node with
     | NullishAssign (name,source,_) ->
       Hashtbl.replace expression_hints source {pos=source;node=Id name}
     | _ -> ());
    List.iter register_expression (Source.children e) in
  List.iter (fun s -> List.iter register_expression (Source.statement_children s)) f.body;
  let env0 = List.map (fun (n,t) ->
    n,if List.exists (assigns n) f.body then cell t else Value (arms declarations t)) f.params in
  { diagnostics; flows; offered; declarations; module_functions; f; assumed; env0;
    executions; expression_hints; rigid_bounds=ref bounds; writes=ref [];
    entries=ref []; expressions=ref []; instantiations=ref []; current_point=ref "";
    contracts=ref []; typing_roots=ref []; evolving=ref []; grown_locals=ref [];
    exact_locals=ref []; closures=ref []; requests=ref []; classes=ref [];
    fresh_constructor=ref false; objects=ref []; exact_allocs=ref []; instances=ref [];
    arrows=ref []; speculative_typing=ref false; block_result=ref (Some f.result);
    block_returned=ref (ref []); following=Hashtbl.create 64 }

module type Scope = sig val state : t end
(* Each component is instantiated once for a pass and closes over that pass.
   Instantiation does not allocate another copy of the analysis state. *)
module View (S : Scope) = struct
  let diagnostics = S.state.diagnostics
  let flows = S.state.flows
  let offered = S.state.offered
  let declarations = S.state.declarations
  let module_functions = S.state.module_functions
  let f = S.state.f
  let assumed = S.state.assumed
  let env0 = S.state.env0
  let rigid_bounds = S.state.rigid_bounds
  let writes = S.state.writes
  let entries = S.state.entries
  let expressions = S.state.expressions
  let instantiations = S.state.instantiations
  let current_point = S.state.current_point
  let contracts = S.state.contracts
  let typing_roots = S.state.typing_roots
  let executions = S.state.executions
  let expression_hints = S.state.expression_hints
  let evolving = S.state.evolving
  let grown_locals = S.state.grown_locals
  let exact_locals = S.state.exact_locals
  let closures = S.state.closures
  let requests = S.state.requests
  let classes = S.state.classes
  let fresh_constructor = S.state.fresh_constructor
  let objects = S.state.objects
  let exact_allocs = S.state.exact_allocs
  let instances = S.state.instances
  let arrows = S.state.arrows
  let speculative_typing = S.state.speculative_typing
  let block_result = S.state.block_result
  let block_returned = S.state.block_returned
  let following = S.state.following
  let for_in_keys = diagnostics.Proposal_diagnostics.for_in_keys
  let method_callees = diagnostics.Proposal_diagnostics.method_callees
  let shape_tests = diagnostics.Proposal_diagnostics.shape_tests
  let undefined_fields = diagnostics.Proposal_diagnostics.undefined_fields
  let dictionary_keys = diagnostics.Proposal_diagnostics.dictionary_keys
  let open_array_tests = diagnostics.Proposal_diagnostics.open_array_tests
  let unknown_instance_tests = diagnostics.Proposal_diagnostics.unknown_instance_tests
  let explain = Proposal_diagnostics.explain diagnostics
  let refuse_length_union = Proposal_diagnostics.refuse_length_union diagnostics
  let rigid_bound r = List.assoc_opt r !rigid_bounds
  let field_type declarations seen t key = Type_queries.field_type !rigid_bounds declarations seen t key
  let index_type declarations seen t key = Type_queries.index_type !rigid_bounds declarations seen t key
  let evolved key = Option.value (List.assoc_opt key assumed) ~default:(Atoms [])
  let evolve key t =
    writes := (key,union (Option.value (List.assoc_opt key !writes) ~default:(Atoms []))
      (widen t)) :: List.remove_assoc key !writes
end
