import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import assert from "node:assert";
import { spawnSync } from "node:child_process";
import { hash } from "../tools/annotate-source.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import type { Ast, Expr, Stmt } from "../tools/fragment.mts";
import type { Labels, Row } from "../tools/type-graph.mts";
import type {
  EntryClaim,
  ExpressionClaim,
  SourceClaims,
} from "../tools/source-claims.mts";
import type { Manifest } from "../report-viewer/types.ts";
import { at as nth, atom, expr as exprOf, must, stmt, written } from "./edits.mts";

/** The claim a document states for one expression's span. */
const claimAt = (d: SourceClaims, pos: readonly number[]) =>
  must(
    must(d.functions[0], "the function's claims").expressions.find(
      (e) => JSON.stringify(e.pos) === JSON.stringify(pos),
    ),
    `a claim at ${pos.join(":")}`,
  );
const __dirname = path.dirname(import.meta.filename);
const verifier=process.argv[2],tmp=fs.mkdtempSync(path.join(os.tmpdir(),"source-claims-"));
/** The expression a statement of this fixture carries. */
const carried = (st: Stmt): Expr => {
  if (st.k === "const" || st.k === "let") return st.init;
  if (st.k === "effect" || st.k === "return") return st.e;
  throw Error(`a ${st.k} statement carries no expression`);
};
/** The one function a handwritten document states claims for. */
const only=(d: SourceClaims)=>must(d.functions[0],"the function's claims");
const run=(exe: string,args: string[])=>{const r=spawnSync(exe,args,{encoding:"utf8"});if(r.error||r.signal)throw r.error||Error(String(r.signal));return r;};
let passed=0;
const test=(name: string,f: () => void)=>{f();passed++;console.log(`  ${name}: OK`);};
try {
  const source="function identity(flag: boolean): boolean { return flag; }\n";
  const file=path.join(tmp,"source.ts"),ap=path.join(tmp,"ast.json"),cp=path.join(tmp,"claims.json"),ep=path.join(tmp,"evidence.json");
  fs.writeFileSync(file,source);
  const parsed=run(process.execPath,[path.resolve(__dirname,"../tools/fragment-parse.mts"),file]);
  assert.equal(parsed.status,0,parsed.stderr);const ast: Ast=JSON.parse(parsed.stdout);fs.writeFileSync(ap,parsed.stdout);
  const f=must(ast.functions[0],"the parsed function"),pos=stmt(nth(f.body,0),"return").e.pos;
  const primitives: Row[]=[["nul"],[{boolLit:{value:true}}],[{boolLit:{value:false}}],["undef"]];
  const doc: SourceClaims={file,sourceSha256:hash(source),types:primitives,functions:[{
    name:f.name,namePos:f.namePos,params:[{name:"flag",type:[1,2],current:null}],result:[1,2],
    entries:[{start:nth(f.body,0).pos[0],bindings:[{name:"flag",type:[1,2],current:null}]}],
    expressions:[{pos,type:[1,2],current:null}]}]};
  fs.writeFileSync(cp,JSON.stringify(doc));
  const produce=()=>run(verifier,["--produce-source-claims",ap,cp,file,ep,"6"]);
  const check=()=>run(verifier,["--check-source-claims",ap,cp,file,ep]);
  test("handwritten calculus claims produce checked evidence",()=>{const r=produce();assert.equal(r.status,0,r.stderr);assert.equal(check().status,0);});
  const mutate=(name: string,edit: (d: SourceClaims) => void)=>test(name,()=>{
    const d=structuredClone(doc);edit(d);fs.writeFileSync(cp,JSON.stringify(d));
    assert.notEqual(check().status,0);assert.notEqual(produce().status,0);
    fs.writeFileSync(cp,JSON.stringify(doc));
  });
  mutate("unknown fields rejected",(d) =>written(d).status="verified");
  mutate("unknown nested fields rejected",(d) =>written(only(d).expressions[0]).proof="trusted");
  mutate("stale source fingerprint rejected",(d) =>d.sourceSha256="0".repeat(64));
  mutate("different source identity rejected",(d) =>d.file="elsewhere.ts");
  mutate("out-of-range labels rejected even in unused bindings",(d) =>must(only(d).entries[0],"an entry").bindings.push({name:"unused",type:[4],current:null}));
  mutate("a table without the primitives is rejected",(d) =>d.types=d.types.slice(1));
  mutate("a table row referring past the table is rejected",(d) =>d.types.push([{refs:{first:[9],rest:[]}}]));
  mutate("duplicate labels rejected",(d) =>only(d).result=[1,1,2]);
  mutate("noncanonical label order rejected",(d) =>only(d).result=[2,1]);
  mutate("duplicate entry sites rejected",(d) =>only(d).entries.push(must(only(d).entries[0],"an entry")));
  mutate("duplicate expression sites rejected",(d) =>only(d).expressions.push(must(only(d).expressions[0],"a claim")));
  mutate("duplicate bindings rejected",(d) =>{const e=must(only(d).entries[0],"an entry");e.bindings.push(must(e.bindings[0],"a binding"));});
  mutate("unrelated entry site rejected",(d) =>only(d).entries.push({start:0,bindings:[]}));
  mutate("unrelated expression site rejected",(d) =>only(d).expressions.push({pos:[0,1],type:[0],current:null}));
  mutate("missing required entry rejected",(d) =>only(d).entries=[]);
  mutate("narrowed entry rejected with old evidence",(d) =>must(must(only(d).entries[0],"an entry").bindings[0],"a binding").type=[1]);
  mutate("false expression claim rejected",(d) =>must(only(d).expressions[0],"a claim").type=[1]);
  mutate("changed signature rejected",(d) =>only(d).result=[1]);
  test("an intersection of arrows is one row, proved per signature",()=>{
    // The corpus fixture SKJS refuses, verified from claims that state the
    // intersection as the source declares it.
    const fixture="verification/tests/skjs-incomplete/arrow-intersection.ts",text=fs.readFileSync(fixture,"utf8");
    const sf=path.join(tmp,"overload.ts"),sa=path.join(tmp,"overload.ast.json"),sc=path.join(tmp,"overload.claims.json"),se=path.join(tmp,"overload.evidence.json");
    const types=[...primitives,[{arrs:{arrows:[[[[1]],[0]],[[[2]],[0]]]}}]];
    // Claims for the parsed program: the lambda and its binding at row 4, the
    // body at the given type, the call at null.
    const write=(source: string,bodyType: Labels)=>{
      fs.writeFileSync(sf,source);
      const p=run(process.execPath,[path.resolve(__dirname,"../tools/fragment-parse.mts"),sf]);assert.equal(p.status,0,p.stderr);
      fs.writeFileSync(sa,p.stdout);
      const parsedAst: Ast=JSON.parse(p.stdout);
      const f=must(parsedAst.functions[0],"the parsed function");
      const cst=stmt(nth(f.body,0),"const"),ret=stmt(nth(f.body,1),"return");
      // The parser writes the second signature under `and` on the first.
      const annot=must(cst.annot,"the binding's annotation");
      assert.deepEqual(annot.atoms.map((x) =>x.a),["function"]);
      assert.equal(must(atom(annot.atoms[0],"function").and,"a second signature").length,1);
      const lambda=exprOf(cst.init,"lambda"),call=exprOf(ret.e,"apply");
      const expressions: ExpressionClaim[]=[{pos:cst.init.pos,type:[4],current:null},{pos:lambda.body.pos,type:bodyType,current:null},
        {pos:ret.e.pos,type:[0],current:null},{pos:call.callee.pos,type:[4],current:null},{pos:must(call.args[0],"an argument").pos,type:[1],current:null}];
      const entries: EntryClaim[]=[{start:cst.pos[0],bindings:[]},{start:ret.pos[0],bindings:[{name:"f",type:[4],current:null}]}];
      fs.writeFileSync(sc,JSON.stringify({file:sf,sourceSha256:hash(source),types,functions:[{name:f.name,namePos:f.namePos,params:[],result:[0],entries,expressions}]}));
    };
    write(text,[0]);
    const produced=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.equal(produced.status,0,produced.stderr);
    assert.equal(run(verifier,["--check-source-claims",sa,sc,sf,se]).status,0);
    // A body that does not meet every signature is refused.
    write(text.replace("=>\n    null;","=> x;"),[1,2]);
    const rejected=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.notEqual(rejected.status,0);
    assert(rejected.stderr.includes("obligation-diagnostic:"),rejected.stderr);
  });
  test("existing SKJS source path checks the same evidence",()=>{
    const boolean={top:false,atoms:[{a:"boolean"}]};
    const sk=path.join(tmp,"skjs.json");
    fs.writeFileSync(sk,JSON.stringify([{file,functions:[{name:f.name,namePos:f.namePos,params:[{name:"flag",type:boolean}],retType:boolean,
      envs:[{pos:f.body[0].pos,vars:[{name:"flag",type:boolean}]}],exprs:[{pos,type:boolean}]}]}]));
    const r=run(verifier,["--check-stateful-source",ap,sk,file,ep]);assert.equal(r.status,0,r.stderr);
  });
  test("restored claims still check",()=>assert.equal(check().status,0));
  test("normalized report verifies without SKJS encoding",()=>{
    const out=path.join(tmp,"report.ts");
    const r=run(process.execPath,[path.resolve(__dirname,"../tools/annotate-source.mts"),file,"--claims",cp,"--format","source-claims","--producer","manual","--verify",verifier,"--out",out]);
    assert.equal(r.status,0,r.stderr);const m: Manifest=JSON.parse(fs.readFileSync(out+".json", "utf8"));
    assert.equal(must(m.results,"results")[0].status,"verified");assert(fs.readFileSync(out,"utf8").includes("entry { flag: boolean }"));
    const changed=structuredClone(doc);must(only(changed).expressions[0],"a claim").type=[1];fs.writeFileSync(cp,JSON.stringify(changed));
    const repaired=path.join(tmp,"changed.ts");
    const compared=run(process.execPath,[path.resolve(__dirname,"../tools/annotate-source.mts"),file,"--claims",cp,"--format","source-claims","--baseline",out+".json","--verify",verifier,"--out",repaired]);
    assert.equal(compared.status,0,compared.stderr);const cm: Manifest=JSON.parse(fs.readFileSync(repaired+".json", "utf8"));
    assert.equal(must(cm.results,"results")[0].status,"not-established");
    const changes=must(cm.comparison,"a comparison").changes;
    assert.equal(changes.length,1);assert.equal(must(changes[0],"a change").kind,"expression");
    fs.writeFileSync(cp,JSON.stringify(doc));
  });
  test("handwritten cell and captured-closure claims verify",()=>{
    const text="function captured(): boolean { const cell: { value: boolean } = { value: true }; const read: (x: null) => boolean = (x: null): boolean => cell.value; cell.value = false; return read(null); }\n";
    const sf=path.join(tmp,"captured.ts"),sa=path.join(tmp,"captured.ast.json"),sc=path.join(tmp,"captured.claims.json"),se=path.join(tmp,"captured.evidence.json");
    fs.writeFileSync(sf,text);
    const p=run(process.execPath,[path.resolve(__dirname,"../tools/fragment-parse.mts"),sf]);assert.equal(p.status,0,p.stderr);
    const a: Ast=JSON.parse(p.stdout),f=must(a.functions[0],"the parsed function");
    const expressions: ExpressionClaim[]=[],entries: EntryClaim[]=[];
    const scope: {name: string; type: Labels; current: null}[]=[];
    // The table: the primitives, then the cell at 4 and the reader arrow at 5.
    const types: Row[]=[...primitives,[{refs:{first:[1,2],rest:[]}}],[{arrs:{arrows:[[[[0]],[1,2]]]}}]];
    const labels: Record<string, Labels>={cell:[4],read:[5],x:[0]};
    const expr=(e: Expr): void =>{
      let type: Labels;
      switch(e.k) {
        case "id":type=must(labels[e.name],`a label for ${e.name}`);break;
        // A literal of this fixture is `true`, `false` or `null`.
        case "lit":type=e.lit.a==="booleanlit"?(e.lit.v==="true"?[1]:[2]):[0];break;
        case "alloc":type=[4];expr(e.e);break;
        case "read":type=[1,2];expr(e.e);break;
        case "lambda":type=[5];expr(e.body);break;
        case "write":type=[2];expr(e.receiver);expr(e.rhs);break;
        case "apply":type=[1,2];expr(e.callee);e.args.forEach(expr);break;
        default:throw Error(`unexpected fixture expression ${e.k}`);
      }
      expressions.push({pos:e.pos,type,current:null});
    };
    for(const st of f.body) {
      entries.push({start:st.pos[0],bindings:structuredClone(scope)});
      expr(carried(st));
      if(st.k==="const")scope.push({name:st.name,type:must(labels[st.name],`a label for ${st.name}`),current:null});
    }
    fs.writeFileSync(sa,p.stdout);fs.writeFileSync(sc,JSON.stringify({file:sf,sourceSha256:hash(text),types,functions:[{name:f.name,namePos:f.namePos,params:[],result:[1,2],entries,expressions}]}));
    const produced=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.equal(produced.status,0,produced.stderr);
    const checked=run(verifier,["--check-source-claims",sa,sc,sf,se]);assert.equal(checked.status,0,checked.stderr);
    const bad: SourceClaims=JSON.parse(fs.readFileSync(sc,"utf8"));
    const reader=exprOf(stmt(nth(f.body,1),"const").init,"lambda");
    const bodyPos=reader.body.pos;
    claimAt(bad,bodyPos).type=[1];
    fs.writeFileSync(sc,JSON.stringify(bad));
    const failed=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);
    assert.notEqual(failed.status,0);
    const diagnostic=readDiagnostic(failed.stderr);
    assert(diagnostic?.kind === "expression-claim");
    assert(diagnostic.sequent);
    assert.equal(diagnostic.sourceMap.role,"expression-claim");
    assert.deepEqual(diagnostic.sourceMap.pos,bodyPos);
    assert.deepEqual(diagnostic.sequent.type,[1]);
    // A closure's heap observation must follow from its invariant for every call.
    // The earlier true allocation cannot justify a permanent true read capability.
    const observed: SourceClaims=JSON.parse(fs.readFileSync(sc,"utf8"));
    claimAt(observed,bodyPos).type=[1,2];
    const receiver=claimAt(observed,exprOf(reader.body,"read").e.pos);
    receiver.current=[1,2];fs.writeFileSync(sc,JSON.stringify(observed));
    const broad=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.equal(broad.status,0,broad.stderr);
    receiver.current=[1];fs.writeFileSync(sc,JSON.stringify(observed));
    assert.notEqual(run(verifier,["--check-source-claims",sa,sc,sf,se]).status,0);
    const stale=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.notEqual(stale.status,0);
    const observation=readDiagnostic(stale.stderr);
    assert(observation?.kind === "expression-claim" && observation.sequent);
    assert.equal(observation.sourceMap.role,"heap-observation");
    assert.deepEqual(observation.sourceMap.pos,receiver.pos);
    assert.deepEqual(observation.sequent.context,[[1,2]]);
    assert.deepEqual(observation.sequent.type,[1]);
  });
  console.log(`Source claims: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
