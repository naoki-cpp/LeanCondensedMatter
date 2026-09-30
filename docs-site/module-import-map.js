export function buildModuleGraphCatalog(modules) {
  const byName = new Map(modules.map((module) => [module.name, module]));
  const importers = new Map([...byName.keys()].map((name) => [name, []]));
  const importsByName = new Map();
  let importCount = 0;

  for (const module of modules) {
    const imports = module.imports
      .filter((name) => byName.has(name))
      .sort((a, b) => a.localeCompare(b));
    importsByName.set(module.name, imports);
    importCount += imports.length;
    for (const imported of imports) importers.get(imported).push(module.name);
  }
  for (const names of importers.values()) names.sort((a, b) => a.localeCompare(b));

  const catalog = modules.map((module) => {
    const dependencies = importsByName.get(module.name) ?? [];
    const dependents = importers.get(module.name) ?? [];
    return {
      ...module,
      name: module.name,
      module: module.name,
      dependencies,
      dependents,
      compiledConsumers: dependents,
      compiledConsumerCount: dependents.length,
      terminal: dependencies.length === 0,
      singleCompiledConsumer: dependents.length === 1,
      directWrapperOf: null,
      retainedMention: false,
      completedMention: false,
      statement: "Lean source module",
      docString: "Imports " + dependencies.length + " project modules; imported by " + dependents.length + " project modules.",
    };
  }).sort((a, b) => a.name.localeCompare(b.name));

  return {
    catalog,
    summary: { moduleCount: catalog.length, importCount },
  };
}
