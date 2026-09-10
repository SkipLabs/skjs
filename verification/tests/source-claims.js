"use strict";
const fs=require("fs"),path=require("path"),os=require("os"),assert=require("assert");
const {spawnSync}=require("child_process"),{hash}=require("../tools/annotate-source.js");
const verifier=process.argv[2],tmp=fs.mkdtempSync(path.join(os.tmpdir(),"source-claims-"));
const run=(exe,args)=>{const r=spawnSync(exe,args,{encoding:"utf8"});if(r.error||r.signal)throw r.error||Error(r.signal);return r;};
let passed=0;
const test=(name,f)=>{f();passed++;console.log(`  ${name}: OK`);};
try {
  const source="function identity(flag: boolean): boolean { return flag; }\n";
  const file=path.join(tmp,"source.ts"),ap=path.join(tmp,"ast.json"),cp=path.join(tmp,"claims.json"),ep=path.join(tmp,"evidence.json");
  fs.writeFileSync(file,source);
  const parsed=run(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),file]);
  assert.equal(parsed.status,0,parsed.stderr);const ast=JSON.parse(parsed.stdout);fs.writeFileSync(ap,parsed.stdout);
  const f=ast.functions[0],pos=f.body[0].e.pos;
  const primitives=[["nul"],[{boolLit:{value:true}}],[{boolLit:{value:false}}],["undef"]];
  const doc={version:3,profile:"stateful-source-v3",file,sourceSha256:hash(source),types:primitives,functions:[{
    name:f.name,namePos:f.namePos,params:[{name:"flag",type:[1,2],current:null}],result:[1,2],
    entries:[{start:f.body[0].pos[0],bindings:[{name:"flag",type:[1,2],current:null}]}],
    expressions:[{pos,type:[1,2],current:null}]}]};
  fs.writeFileSync(cp,JSON.stringify(doc));
  const produce=()=>run(verifier,["--produce-source-claims",ap,cp,file,ep,"6"]);
  const check=()=>run(verifier,["--check-source-claims",ap,cp,file,ep]);
  test("handwritten calculus claims produce checked evidence",()=>{const r=produce();assert.equal(r.status,0,r.stderr);assert.equal(check().status,0);});
  const mutate=(name,edit)=>test(name,()=>{
    const d=structuredClone(doc);edit(d);fs.writeFileSync(cp,JSON.stringify(d));
    assert.notEqual(check().status,0);assert.notEqual(produce().status,0);
    fs.writeFileSync(cp,JSON.stringify(doc));
  });
  mutate("unknown fields rejected",d=>d.status="verified");
  mutate("unknown nested fields rejected",d=>d.functions[0].expressions[0].proof="trusted");
  mutate("stale source fingerprint rejected",d=>d.sourceSha256="0".repeat(64));
  mutate("different source identity rejected",d=>d.file="elsewhere.ts");
  mutate("unsupported graph profile rejected",d=>d.profile="arbitrary");
  mutate("retired profile is rejected",d=>d.profile="stateful-source-19-v1");
  mutate("previous fixed-table profile is rejected",d=>d.profile="stateful-source-532-v2");
  mutate("out-of-range labels rejected even in unused bindings",d=>d.functions[0].entries[0].bindings.push({name:"unused",type:[4],current:null}));
  mutate("a table without the primitives is rejected",d=>d.types=d.types.slice(1));
  mutate("a table row referring past the table is rejected",d=>d.types.push([{refs:{first:[9],rest:[]}}]));
  mutate("duplicate labels rejected",d=>d.functions[0].result=[1,1,2]);
  mutate("noncanonical label order rejected",d=>d.functions[0].result=[2,1]);
  mutate("duplicate entry sites rejected",d=>d.functions[0].entries.push(d.functions[0].entries[0]));
  mutate("duplicate expression sites rejected",d=>d.functions[0].expressions.push(d.functions[0].expressions[0]));
  mutate("duplicate bindings rejected",d=>d.functions[0].entries[0].bindings.push(d.functions[0].entries[0].bindings[0]));
  mutate("unrelated entry site rejected",d=>d.functions[0].entries.push({start:0,bindings:[]}));
  mutate("unrelated expression site rejected",d=>d.functions[0].expressions.push({pos:[0,1],type:[0]}));
  mutate("missing required entry rejected",d=>d.functions[0].entries=[]);
  mutate("narrowed entry rejected with old evidence",d=>d.functions[0].entries[0].bindings[0].type=[1]);
  mutate("false expression claim rejected",d=>d.functions[0].expressions[0].type=[1]);
  mutate("changed signature rejected",d=>d.functions[0].result=[1]);
  test("an intersection of arrows is one row, proved per signature",()=>{
    // The corpus fixture SKJS refuses, verified from claims that state the
    // intersection as the source declares it.
    const fixture="verification/tests/skjs-incomplete/arrow-intersection.ts",text=fs.readFileSync(fixture,"utf8");
    const sf=path.join(tmp,"overload.ts"),sa=path.join(tmp,"overload.ast.json"),sc=path.join(tmp,"overload.claims.json"),se=path.join(tmp,"overload.evidence.json");
    const types=[...primitives,[{arrs:{arrows:[[[1],[0]],[[2],[0]]]}}]];
    // Claims for the parsed program: the lambda and its binding at row 4, the
    // body at the given type, the call at null.
    const write=(source,bodyType)=>{
      fs.writeFileSync(sf,source);
      const p=run(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),sf]);assert.equal(p.status,0,p.stderr);
      fs.writeFileSync(sa,p.stdout);
      const f=JSON.parse(p.stdout).functions[0],[cst,ret]=f.body;
      // The parser writes the second signature under `and` on the first.
      assert.deepEqual(cst.annot.atoms.map(x=>x.a),["function"]);assert.equal(cst.annot.atoms[0].and.length,1);
      const expressions=[{pos:cst.init.pos,type:[4],current:null},{pos:cst.init.body.pos,type:bodyType,current:null},
        {pos:ret.e.pos,type:[0],current:null},{pos:ret.e.callee.pos,type:[4],current:null},{pos:ret.e.arg.pos,type:[1],current:null}];
      const entries=[{start:cst.pos[0],bindings:[]},{start:ret.pos[0],bindings:[{name:"f",type:[4],current:null}]}];
      fs.writeFileSync(sc,JSON.stringify({version:3,profile:doc.profile,file:sf,sourceSha256:hash(source),types,functions:[{name:f.name,namePos:f.namePos,params:[],result:[0],entries,expressions}]}));
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
    const r=run(process.execPath,[path.resolve(__dirname,"../tools/annotate-source.js"),file,"--claims",cp,"--format","source-claims","--producer","manual","--verify",verifier,"--out",out]);
    assert.equal(r.status,0,r.stderr);const m=JSON.parse(fs.readFileSync(out+".json"));
    assert.equal(m.results[0].status,"verified");assert(fs.readFileSync(out,"utf8").includes("true | false"));
    const changed=structuredClone(doc);changed.functions[0].expressions[0].type=[1];fs.writeFileSync(cp,JSON.stringify(changed));
    const repaired=path.join(tmp,"changed.ts");
    const compared=run(process.execPath,[path.resolve(__dirname,"../tools/annotate-source.js"),file,"--claims",cp,"--format","source-claims","--baseline",out+".json","--verify",verifier,"--out",repaired]);
    assert.equal(compared.status,0,compared.stderr);const cm=JSON.parse(fs.readFileSync(repaired+".json"));
    assert.equal(cm.results[0].status,"not-established");assert.equal(cm.comparison.changes.length,1);assert.equal(cm.comparison.changes[0].kind,"expression");
    fs.writeFileSync(cp,JSON.stringify(doc));
  });
  test("handwritten cell and captured-closure claims verify",()=>{
    const text="function captured(): boolean { const cell: { value: boolean } = { value: true }; const read: (x: null) => boolean = (x: null): boolean => cell.value; cell.value = false; return read(null); }\n";
    const sf=path.join(tmp,"captured.ts"),sa=path.join(tmp,"captured.ast.json"),sc=path.join(tmp,"captured.claims.json"),se=path.join(tmp,"captured.evidence.json");
    fs.writeFileSync(sf,text);
    const p=run(process.execPath,[path.resolve(__dirname,"../tools/parse-source.js"),sf]);assert.equal(p.status,0,p.stderr);
    const a=JSON.parse(p.stdout),f=a.functions[0],expressions=[],entries=[],scope=[];
    // The table: the primitives, then the cell at 4 and the reader arrow at 5.
    const types=[...primitives,[{refs:{first:[1,2],rest:[]}}],[{arrs:{arrows:[[[0],[1,2]]]}}]];
    const labels={cell:[4],read:[5],x:[0]};
    const expr=e=>{
      let type;
      switch(e.k) {
        case "id":type=labels[e.name];break;
        case "lit":type=e.lit.v==="true"?[1]:e.lit.v==="false"?[2]:[0];break;
        case "alloc":type=[4];expr(e.e);break;
        case "read":type=[1,2];expr(e.e);break;
        case "lambda":type=[5];expr(e.body);break;
        case "write":type=[2];expr(e.receiver);expr(e.rhs);break;
        case "apply":type=[1,2];expr(e.callee);expr(e.arg);break;
        default:throw Error(`unexpected fixture expression ${e.k}`);
      }
      expressions.push({pos:e.pos,type,current:null});
    };
    for(const st of f.body) {
      entries.push({start:st.pos[0],bindings:structuredClone(scope)});
      expr(st.init||st.e);
      if(st.k==="const")scope.push({name:st.name,type:labels[st.name],current:null});
    }
    fs.writeFileSync(sa,p.stdout);fs.writeFileSync(sc,JSON.stringify({version:3,profile:doc.profile,file:sf,sourceSha256:hash(text),types,functions:[{name:f.name,namePos:f.namePos,params:[],result:[1,2],entries,expressions}]}));
    const produced=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.equal(produced.status,0,produced.stderr);
    const checked=run(verifier,["--check-source-claims",sa,sc,sf,se]);assert.equal(checked.status,0,checked.stderr);
    const bad=JSON.parse(fs.readFileSync(sc,"utf8"));
    const bodyPos=f.body[1].init.body.pos;
    bad.functions[0].expressions.find(e=>JSON.stringify(e.pos)===JSON.stringify(bodyPos)).type=[1];
    fs.writeFileSync(sc,JSON.stringify(bad));
    const failed=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);
    assert.notEqual(failed.status,0);
    const diagnostic=require("../tools/obligation-diagnostic.js").readDiagnostic(failed.stderr);
    assert.equal(diagnostic.kind,"expression-claim");
    assert.equal(diagnostic.sourceMap.role,"expression-claim");
    assert.deepEqual(diagnostic.sourceMap.pos,bodyPos);
    assert.deepEqual(diagnostic.sequent.type,[1]);
    // A closure's heap observation must follow from its invariant for every call.
    // The earlier true allocation cannot justify a permanent true read capability.
    const observed=JSON.parse(fs.readFileSync(sc,"utf8"));
    const cf=observed.functions[0];
    cf.expressions.find(e=>JSON.stringify(e.pos)===JSON.stringify(bodyPos)).type=[1,2];
    const receiver=cf.expressions.find(e=>JSON.stringify(e.pos)===JSON.stringify(f.body[1].init.body.e.pos));
    receiver.current=[1,2];fs.writeFileSync(sc,JSON.stringify(observed));
    const broad=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.equal(broad.status,0,broad.stderr);
    receiver.current=[1];fs.writeFileSync(sc,JSON.stringify(observed));
    assert.notEqual(run(verifier,["--check-source-claims",sa,sc,sf,se]).status,0);
    const stale=run(verifier,["--produce-source-claims",sa,sc,sf,se,"10"]);assert.notEqual(stale.status,0);
    const observation=require("../tools/obligation-diagnostic.js").readDiagnostic(stale.stderr);
    assert.equal(observation.sourceMap.role,"heap-observation");
    assert.deepEqual(observation.sourceMap.pos,receiver.pos);
    assert.deepEqual(observation.sequent.context,[[1,2]]);
    assert.deepEqual(observation.sequent.type,[1]);
  });
  console.log(`Source claims: ${passed} passed, 0 failed`);
} finally {fs.rmSync(tmp,{recursive:true,force:true});}
