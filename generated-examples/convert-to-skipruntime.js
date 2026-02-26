#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

const GENERATED_EXAMPLES_DIR = __dirname;

// Skip these directories (already converted or not services)
const SKIP_DIRS = [
  'skipruntime',
  'counter-service-api',
  'node_modules',
  'chat-room-service',  // Already manually converted
  'todo-list-api',      // Already manually converted
];

function getServiceDirs() {
  return fs.readdirSync(GENERATED_EXAMPLES_DIR)
    .filter(name => {
      const fullPath = path.join(GENERATED_EXAMPLES_DIR, name);
      return fs.statSync(fullPath).isDirectory() &&
             !SKIP_DIRS.includes(name) &&
             fs.existsSync(path.join(fullPath, 'src', 'service.ts'));
    });
}

function createSymlink(serviceDir) {
  const symlinkPath = path.join(serviceDir, 'skipruntime');
  if (fs.existsSync(symlinkPath)) {
    try { fs.unlinkSync(symlinkPath); } catch {}
  }
  fs.symlinkSync('../skipruntime', symlinkPath);
  console.log(`  Created symlink: skipruntime`);
}

function updateTsconfig(serviceDir) {
  const tsconfigPath = path.join(serviceDir, 'tsconfig.json');
  if (!fs.existsSync(tsconfigPath)) {
    console.log(`  Warning: No tsconfig.json found`);
    return;
  }

  let content = fs.readFileSync(tsconfigPath, 'utf8');

  // Change rootDir from "src" or "${configDir}/src" or "./src" to "."
  content = content.replace(/"rootDir":\s*"\$\{configDir\}\/src"/, '"rootDir": "."');
  content = content.replace(/"rootDir":\s*"\.\/src"/, '"rootDir": "."');
  content = content.replace(/"rootDir":\s*"src"/, '"rootDir": "."');

  // Update include to add skipruntime/core.ts
  content = content.replace(
    /"include":\s*\[\s*"src\/\*\*\/\*\.ts"\s*\]/,
    '"include": ["src/**/*.ts", "skipruntime/core.ts"]'
  );

  fs.writeFileSync(tsconfigPath, content);
  console.log(`  Updated tsconfig.json`);
}

function escapeRegex(str) {
  return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function convertServiceTs(serviceDir) {
  const servicePath = path.join(serviceDir, 'src', 'service.ts');
  if (!fs.existsSync(servicePath)) {
    console.log(`  Warning: No service.ts found`);
    return;
  }

  let content = fs.readFileSync(servicePath, 'utf8');

  // Step 1: Parse the original Inputs type to extract input names and types
  // Match only the Inputs type, not InputCollections
  const inputsMatch = content.match(/^type\s+Inputs\s*=\s*\{([^}]+)\}/m);
  const inputs = [];
  if (inputsMatch) {
    // Match: name: Entry<K, V>[]
    const entryRegex = /(\w+):\s*Entry<([^,>]+),\s*([^>]+)>\[\]/g;
    let m;
    while ((m = entryRegex.exec(inputsMatch[1])) !== null) {
      inputs.push({ name: m[1], keyType: m[2].trim(), valueType: m[3].trim() });
    }
  }

  // Step 2: Parse Resources type to extract resource names
  const resourcesMatch = content.match(/^type\s+Resources\s*=\s*\{([^}]+)\}/m);
  const resources = [];
  if (resourcesMatch) {
    // Match: "name-with-hyphens" or name: new (params: Json) => Resource<...>
    const resourceRegex = /["']([\w-]+)["']:\s*new\s*\([^)]*\)\s*=>\s*Resource<[^>]+>/g;
    let m;
    while ((m = resourceRegex.exec(resourcesMatch[1])) !== null) {
      resources.push(m[1]);
    }
    // Also try unquoted names (may be indented)
    const unquotedRegex = /^\s*(\w+):\s*new\s*\([^)]*\)\s*=>\s*Resource<[^>]+>/gm;
    while ((m = unquotedRegex.exec(resourcesMatch[1])) !== null) {
      if (!resources.includes(m[1])) {
        resources.push(m[1]);
      }
    }
  }

  // Step 3: Update imports
  const importTypeMatch = content.match(/import\s+type\s*\{([^}]+)\}\s*from\s*["']@skipruntime\/core["'];?/);
  if (importTypeMatch) {
    let types = importTypeMatch[1]
      .split(',')
      .map(s => s.trim())
      .filter(s => s && s !== 'Entry'); // Keep Json if present, only remove Entry

    // Add ResourceClass if not present
    if (!types.includes('ResourceClass')) {
      const resourceIdx = types.indexOf('Resource');
      if (resourceIdx !== -1) {
        types.splice(resourceIdx + 1, 0, 'ResourceClass');
      } else {
        types.push('ResourceClass');
      }
    }

    const newTypeImport = `import type {\n  ${types.join(',\n  ')}\n} from "../skipruntime/core.js";`;
    const valueImport = `import { InputDefinition } from "../skipruntime/core.js";`;

    content = content.replace(
      /import\s+type\s*\{[^}]+\}\s*from\s*["']@skipruntime\/core["'];?/,
      newTypeImport + '\n' + valueImport
    );
  }

  // Step 4: Update Inputs type ONLY - Entry<K, V>[] -> InputDefinition<K, V>
  // Be very specific: only in the Inputs type block
  if (inputsMatch) {
    let newInputsType = inputsMatch[0];
    for (const input of inputs) {
      const pattern = new RegExp(`(${input.name}:\\s*)Entry<${escapeRegex(input.keyType)},\\s*${escapeRegex(input.valueType)}>\\[\\]`, 'g');
      newInputsType = newInputsType.replace(pattern, `$1InputDefinition<${input.keyType}, ${input.valueType}>`);
    }
    content = content.replace(inputsMatch[0], newInputsType);
  }

  // Step 5: Export Inputs type
  content = content.replace(/^type Inputs\s*=/gm, 'export type Inputs =');

  // Step 6: Update Resources type
  // Build a map from resource name -> constructor param type by:
  // 1. Finding `this.resources = { "name": ClassName, ... }`
  // 2. Finding each class's constructor param type
  const resourceParamTypes = {};
  // Parse this.resources assignment to get name -> className mapping
  const resourcesAssignRegex = /["']?([\w-]+)["']?\s*:\s*(\w+)/g;
  const resourcesAssignMatch = content.match(/this\.(?:resources|initialData)\s*=\s*\{[^}]*\}/g);
  const resourcesAssign = content.match(/this\.resources\s*=\s*\{([^}]+)\}/);
  if (resourcesAssign) {
    let m;
    while ((m = resourcesAssignRegex.exec(resourcesAssign[1])) !== null) {
      const resourceName = m[1];
      const className = m[2];
      // Find the class constructor param type
      const ctorRegex = new RegExp(`class\\s+${className}[^{]*\\{[\\s\\S]*?constructor\\s*\\(([^)]*)\\)`, 'm');
      const ctorMatch = content.match(ctorRegex);
      if (ctorMatch) {
        const paramStr = ctorMatch[1].trim();
        if (!paramStr || paramStr.startsWith('_params')) {
          // Unused params or no params -> {}
          resourceParamTypes[resourceName] = '{}';
        } else {
          // Extract the type from "params: SomeType" or "params: SomeType = default"
          const typeMatch = paramStr.match(/\w+:\s*([^=,]+)/);
          if (typeMatch) {
            const paramType = typeMatch[1].trim();
            if (paramType === 'Json') {
              resourceParamTypes[resourceName] = '{}';
            } else {
              resourceParamTypes[resourceName] = paramType;
            }
          } else {
            resourceParamTypes[resourceName] = '{}';
          }
        }
      } else {
        resourceParamTypes[resourceName] = '{}';
      }
    }
  }

  // Sort by length descending so longer names (like "webhooks-deliveries") are processed before shorter ones ("deliveries")
  if (resourcesMatch) {
    let newResourcesType = resourcesMatch[0];
    const sortedResources = resources.slice().sort((a, b) => b.length - a.length);
    for (const resourceName of sortedResources) {
      const paramType = resourceParamTypes[resourceName] || '{}';
      // Handle quoted resource names - require quotes to avoid partial matches
      const escapedName = escapeRegex(resourceName);
      const pattern = new RegExp(`["']${escapedName}["']:\\s*new\\s*\\([^)]*\\)\\s*=>\\s*Resource<[^>]+>`, 'g');
      newResourcesType = newResourcesType.replace(pattern, `"${resourceName}": ResourceClass<GraphCollections, ${paramType}>`);
    }
    // Also handle unquoted names (rare)
    for (const resourceName of sortedResources) {
      if (!resourceName.includes('-')) {
        const paramType = resourceParamTypes[resourceName] || '{}';
        const pattern = new RegExp(`(?<![\\w-])${resourceName}:\\s*new\\s*\\([^)]*\\)\\s*=>\\s*Resource<[^>]+>`, 'g');
        newResourcesType = newResourcesType.replace(pattern, `"${resourceName}": ResourceClass<GraphCollections, ${paramType}>`);
      }
    }
    // Handle index signature pattern: [name: string]: new (params: Json) => Resource<...>
    newResourcesType = newResourcesType.replace(
      /\[name:\s*string\]:\s*new\s*\([^)]*\)\s*=>\s*Resource<[^>]+>/g,
      '[name: string]: ResourceClass<GraphCollections, Json>'
    );
    content = content.replace(resourcesMatch[0], newResourcesType);
  }

  // Step 7: Export Resources type
  content = content.replace(/^type Resources\s*=/gm, 'export type Resources =');

  // Step 8: Update SkipService generic parameters
  content = content.replace(
    /implements\s+SkipService<InputCollections,\s*GraphCollections>/g,
    'implements SkipService<Inputs, InputCollections, GraphCollections, Resources>'
  );
  content = content.replace(
    /:\s*SkipService<InputCollections,\s*GraphCollections>/g,
    ': SkipService<Inputs, InputCollections, GraphCollections, Resources>'
  );

  // Step 9: Change initialData to inputs
  content = content.replace(/public\s+initialData:\s*Inputs;?/g, 'public inputs: Inputs;');
  content = content.replace(/this\.initialData\s*=/g, 'this.inputs =');

  // Step 10: Update constructor - remove Entry<K,V>[] declarations and update inputs object
  // Remove lines like: const emptyX: Entry<K, V>[] = Array.of();
  content = content.replace(/const\s+\w+:\s*Entry<[^>]+>\[\]\s*=\s*Array\.of\(\);?\s*\n/g, '');

  // Update this.inputs = { name: emptyX } to { name: new InputDefinition<K, V>([]) }
  for (const input of inputs) {
    // Match: inputName: variableName followed by comma or closing brace
    const pattern = new RegExp(`(${input.name}:\\s*)(\\w+)(?=[,}\\s])`, 'g');
    content = content.replace(pattern, (match, prefix, varName) => {
      // Only replace if the variable name looks like "emptyX" or similar
      if (varName.startsWith('empty') || varName === input.name) {
        return `${prefix}new InputDefinition<${input.keyType}, ${input.valueType}>([])`;
      }
      return match;
    });
  }

  // Step 11: Update Resource constructor params: Json -> {} for unused params
  // But keep as Json if using index signature pattern (ResourceClass<G, Json>)
  const usesIndexSignature = /\[name:\s*string\]:\s*ResourceClass/.test(content);
  content = content.replace(
    /constructor\s*\(\s*params:\s*Json\s*=\s*\{\}\s*\)/g,
    'constructor(params: Json)'
  );
  if (!usesIndexSignature) {
    content = content.replace(
      /constructor\s*\(\s*_params:\s*Json\s*=\s*\{\}\s*\)/g,
      'constructor(_params: {})'
    );
    content = content.replace(
      /constructor\s*\(\s*_params:\s*Json\s*\)/g,
      'constructor(_params: {})'
    );
  }

  // Step 12: Convert indexed loops with arr[i]! to for...of
  content = convertIndexedLoops(content);

  fs.writeFileSync(servicePath, content);
  console.log(`  Converted service.ts`);
}

function convertIndexedLoops(content) {
  // Pattern for the indexed loop:
  // const arr = values.toArray();
  // const result: Array<...> = Array.of();
  // for (let i = 0; i < arr.length; i++) {
  //   const v = arr[i]!;
  //   ...body...
  // }

  const loopPattern = /const\s+arr\s*=\s*values\.toArray\(\);\s*\n(\s*)(const\s+result[^;]+;)\s*\n\s*for\s*\(\s*let\s+i\s*=\s*0;\s*i\s*<\s*arr\.length;\s*i\+\+\s*\)\s*\{\s*\n\s*const\s+(\w+)\s*=\s*arr\[i\]!;/g;

  content = content.replace(loopPattern, (match, indent, resultDecl, varName) => {
    return `${resultDecl}\n${indent}for (const ${varName} of values) {`;
  });

  return content;
}

function runTsc(serviceDir) {
  const { execSync } = require('child_process');
  try {
    execSync('npx tsc --noEmit', { cwd: serviceDir, stdio: 'pipe' });
    console.log(`  ✓ tsc passed`);
    return true;
  } catch (error) {
    console.log(`  ✗ tsc failed:`);
    const output = error.stdout?.toString() || error.stderr?.toString() || error.message;
    const lines = output.split('\n').slice(0, 20);
    console.log(lines.join('\n'));
    if (output.split('\n').length > 20) {
      console.log(`  ... and ${output.split('\n').length - 20} more lines`);
    }
    return false;
  }
}

function restoreService(serviceDir) {
  const { execSync } = require('child_process');
  const servicePath = path.join(serviceDir, 'src', 'service.ts');
  const tsconfigPath = path.join(serviceDir, 'tsconfig.json');
  const symlinkPath = path.join(serviceDir, 'skipruntime');
  const tsbuildInfoPath = path.join(serviceDir, 'tsconfig.tsbuildinfo');

  // Restore files from git
  try {
    execSync(`git checkout -- "${servicePath}" "${tsconfigPath}"`, {
      cwd: GENERATED_EXAMPLES_DIR,
      stdio: 'pipe',
    });
    console.log(`  Restored service.ts and tsconfig.json`);
  } catch (error) {
    console.log(`  Warning: Could not restore from git: ${error.message}`);
  }

  // Remove symlink
  if (fs.existsSync(symlinkPath)) {
    try {
      fs.unlinkSync(symlinkPath);
      console.log(`  Removed skipruntime symlink`);
    } catch (error) {
      console.log(`  Warning: Could not remove symlink: ${error.message}`);
    }
  }

  // Remove tsbuildinfo
  if (fs.existsSync(tsbuildInfoPath)) {
    try {
      fs.unlinkSync(tsbuildInfoPath);
    } catch {}
  }
}

function main() {
  const args = process.argv.slice(2);
  const dryRun = args.includes('--dry-run');
  const checkOnly = args.includes('--check');
  const restore = args.includes('--restore');
  const singleService = args.find(a => !a.startsWith('--'));

  let serviceDirs = getServiceDirs();

  if (singleService) {
    serviceDirs = serviceDirs.filter(d => d === singleService);
    if (serviceDirs.length === 0) {
      console.log(`Service not found: ${singleService}`);
      process.exit(1);
    }
  }

  const action = restore ? 'restore' : 'convert';
  console.log(`Found ${serviceDirs.length} services to ${action}\n`);

  let passed = 0;
  let failed = 0;

  for (const dirName of serviceDirs) {
    const serviceDir = path.join(GENERATED_EXAMPLES_DIR, dirName);
    console.log(`${restore ? 'Restoring' : 'Converting'} ${dirName}...`);

    if (dryRun) {
      console.log(`  (dry run - skipping)`);
      continue;
    }

    if (restore) {
      restoreService(serviceDir);
      passed++;
      console.log('');
      continue;
    }

    try {
      createSymlink(serviceDir);
      updateTsconfig(serviceDir);
      convertServiceTs(serviceDir);

      if (checkOnly) {
        passed++;
      } else if (runTsc(serviceDir)) {
        passed++;
      } else {
        failed++;
      }
    } catch (error) {
      console.log(`  Error: ${error.message}`);
      failed++;
    }

    console.log('');
  }

  console.log(`\nResults: ${passed} passed, ${failed} failed`);
}

main();
