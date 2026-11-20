import { NodeType } from "../asttype.js";
import type { SurvivalAccess } from "./access.js";
import { Assertion } from "./core/assert.js";
import { AST, type MatchTable } from "./core/ast.js";
import { HilbertSystem } from "./core/core.js";
import { type Deduction, type Proposition } from "./core/deduction.js";
import { HSParser } from "./core/parser.js";

const namePattern = /^[a-z][A-Za-z0-9_]*$/;
const variablePattern = /^[$#]?[a-z][A-Za-z0-9_]*$/;
const holePrefix = "\0";
const isHole = (ast: AST) => ast.name.startsWith(holePrefix);
const hasHole = (ast: AST): boolean => isHole(ast) || ast.nodes.some(hasHole);
const implication = (ast: AST) => ast.type === NodeType.LOGIC && ast.name === ">";
const fail = (message: string): never => { throw new Error(message); };

function resolve(ast: AST, values: ReadonlyMap<string, AST>): AST {
    const value = isHole(ast) ? values.get(ast.name) : undefined;
    return value ? resolve(value, values) : new AST(ast.type, ast.name, ...ast.nodes.map(n => resolve(n, values)));
}

// Native formulas (including every user-written $name) are rigid. Only nodes
// allocated while instantiating a rule participate in assistant unification.
function reduceSubstitution(ast: AST): AST {
    if (!ast.hasSbFn()) return ast;
    const reduced = ast.clone();
    Assertion.reduceSbFn([], reduced);
    return reduced;
}

function unify(left: AST, right: AST, values: Map<string, AST>) {
    left = resolve(left, values);
    right = resolve(right, values);
    // Do not interpret uninstantiated rule slots as native variable names.
    if (left.type === NodeType.SB && !hasHole(left)) left = reduceSubstitution(left);
    if (right.type === NodeType.SB && !hasHole(right)) right = reduceSubstitution(right);
    const occurs = (name: string, term: AST): boolean => term.name === name || term.nodes.some(n => occurs(name, n));
    if (left.equal(right)) return;
    if (!isHole(left) && isHole(right)) return unify(right, left, values);
    if (isHole(left)) {
        if (occurs(left.name, right)) fail("Circular rule argument.");
        if (isHole(right)) {
            if (left.type !== right.type) fail("Rule arguments have incompatible sorts.");
        } else if (left.type === NodeType.ATOM_ITEM) right.checkITEM();
        else right.checkWFF();
        values.set(left.name, right);
        return;
    }
    if (left.type !== right.type || left.name !== right.name || left.nodes.length !== right.nodes.length) {
        fail("The source does not match the goal or premise.");
    }
    for (let i = 0; i < left.nodes.length; i++) unify(left.nodes[i], right.nodes[i], values);
}

// Renaming applies to free occurrences only. Intro's alias is not a change to
// the kernel binder, and must not become captured when a formula is entered.
function renameFreeItems(ast: AST, aliases: ReadonlyMap<string, string>, bound = new Set<string>()): AST {
    if (ast.type === NodeType.ATOM_ITEM && !bound.has(ast.name)) {
        const name = aliases.get(ast.name);
        if (name !== undefined) {
            if (bound.has(name)) fail(`Variable ${ast.name} would be captured by ${name}.`);
            return new AST(ast.type, name);
        }
    }
    const binder = ast.getBoundVarName();
    const body = ast.type === NodeType.RPL ? 0 : ast.type === NodeType.BOUNDED_QUANT || ast.type === NodeType.SEP ? 2 : 1;
    const binderIndex = ast.type === NodeType.RPL ? 1 : 0;
    return new AST(ast.type, ast.name, ...ast.nodes.map((n, i) => {
        if (binder === undefined) return renameFreeItems(n, aliases, bound);
        if (i === binderIndex) return n.clone();
        return renameFreeItems(n, aliases, i === body ? new Set([...bound, binder]) : bound);
    }));
}

interface Binding { id: number; formula: AST }
interface Goal {
    id: number;
    target: AST;
    bindings: ReadonlyMap<string, Binding>;
    variables: ReadonlyMap<string, string>;
}
type Source = { kind: "binding"; id: number } | {
    kind: "rule"; name: AST; slots: Map<string, AST>; inputs: Source[];
};
type Action =
    | { kind: "exact"; source: Source }
    | { kind: "intro"; folder: "c" | "v"; ast: AST; child: Goal }
    | { kind: "let"; source: Source; next: Goal }
    | { kind: "goal"; lemma: Goal; next: Goal }
    | { kind: "apply"; source: Source; children: Goal[]; useMp: boolean };
interface Draft {
    pending: Goal[];
    actions: Map<number, Action>;
    values: Map<string, AST>;
    nextId: number;
}

export class HilbertProofAssistant {
    private parser = new HSParser();
    private readonly root: Goal;
    private draft: Draft;
    private recorded = false;

    constructor(private readonly system: HilbertSystem, target: string, private readonly access?: SurvivalAccess) {
        const ast = this.formula(target.trim());
        this.root = { id: 0, target: ast, bindings: new Map(), variables: new Map() };
        this.draft = { pending: [this.root], actions: new Map(), values: new Map(), nextId: 1 };
    }

    snapshot() {
        const show = (ast: AST, goal: Goal) => {
            const resolved = resolve(ast, this.draft.values);
            const aliases = new Map([...goal.variables].map(([alias, binder]) => [binder, alias]));
            let displayed: AST;
            try { displayed = renameFreeItems(resolved, aliases); } catch { displayed = resolved; }
            const simplifyHoles = (a: AST) => {
                if (isHole(a)) a.name = `?${a.name.slice(holePrefix.length).replace(":", "_")}`;
                a.nodes.forEach(simplifyHoles);
            };
            simplifyHoles(displayed);
            return displayed.toString();
        };
        return {
            target: this.root.target.toString(),
            goals: this.draft.pending.map(goal => ({
                target: show(goal.target, goal),
                context: [...goal.variables].map(([name]) => ({ name, formula: null as string | null }))
                    .concat([...goal.bindings].map(([name, binding]) => ({ name, formula: show(binding.formula, goal) }))),
            })),
        };
    }

    execute(text: string) {
        const [, command, argument = ""] = /^([a-z]+)(?:\s+([^\r\n]*))?$/.exec(text.trim()) ?? [];
        const [current, ...remaining] = this.draft.pending;
        if (!current) return fail("The proof is complete. Use qed to record it.");
        const draft: Draft = {
            pending: remaining, actions: new Map(this.draft.actions),
            values: new Map(this.draft.values), nextId: this.draft.nextId,
        };
        const target = resolve(current.target, draft.values);
        const subgoal = (formula: AST, bindings = current.bindings, variables = current.variables): Goal =>
            ({ id: draft.nextId++, target: formula, bindings, variables });
        const withBinding = (name: string, id: number, formula: AST) => new Map([...current.bindings, [name, { id, formula }]]);
        const set = (action: Action, ...next: Goal[]) => {
            draft.actions.set(current.id, action);
            draft.pending.unshift(...next);
        };
        if (command === "intro") {
            if (implication(target)) {
                this.checkFresh(argument, current);
                const child = subgoal(target.nodes[1], withBinding(argument, current.id, target.nodes[0]));
                set({ kind: "intro", folder: "c", ast: target.nodes[0], child }, child);
            } else if (target.type === NodeType.QUANT && target.name === "\\a") {
                this.checkFresh(argument, current, true);
                const binder = target.nodes[0];
                if (hasHole(binder)) return fail("The quantified variable must be determined before intro.");
                if ([...current.variables.values()].includes(binder.name)) return fail("Rename the shadowed quantifier before intro.");
                const mentions = (node: AST): boolean => node.name === argument || node.nodes.some(mentions);
                if (argument !== binder.name && (mentions(target) || [...current.bindings.values()].some(b => mentions(b.formula))
                    || [...current.variables.values()].includes(argument))) return fail("Choose a fresh variable name.");
                const child = subgoal(target.nodes[1], current.bindings, new Map([...current.variables, [argument, binder.name]]));
                set({ kind: "intro", folder: "v", ast: binder, child }, child);
            } else return fail("Intro requires an implication or a universal quantifier.");
        } else if (command === "goal") {
            const match = /^(\S+)\s*:\s*(.+)$/.exec(argument);
            if (!match) return fail("Use goal name : formula.");
            const [, name, text] = match;
            this.checkFresh(name, current);
            const lemma = subgoal(this.formula(text, current));
            const next = subgoal(current.target, withBinding(name, lemma.id, lemma.target));
            set({ kind: "goal", lemma, next }, lemma, next);
        } else if (command === "let") {
            const match = /^(\S+)\s*:=\s*(.+)$/.exec(argument);
            if (!match) return fail("Use let name := source.");
            const [, name, text] = match;
            this.checkFresh(name, current);
            const expression = this.source(text, current, draft, false);
            const next = subgoal(current.target, withBinding(name, current.id, expression.conclusion));
            set({ kind: "let", source: expression.source, next }, next);
        } else if (command === "exact" || command === "apply") {
            const expression = this.source(argument, current, draft, command === "apply");
            let conclusion = resolve(expression.conclusion, draft.values);
            const premises = expression.premises.slice();
            const useMp = command === "apply" && expression.source.kind === "binding";
            // A local proof is rigid; only the goal's unsolved rule slots
            // may be inferred when trying its successive implication tails.
            while (useMp && implication(conclusion)) {
                const trial = new Map(draft.values);
                try { unify(target, conclusion, trial); } catch {
                    premises.push(conclusion.nodes[0]);
                    conclusion = conclusion.nodes[1];
                    continue;
                }
                break;
            }
            unify(target, conclusion, draft.values);
            if (command === "exact") set({ kind: "exact", source: expression.source });
            else {
                const children = premises.map(ast => subgoal(ast));
                set({ kind: "apply", source: expression.source, children, useMp }, ...children);
            }
        } else return fail("Use intro, exact, apply, goal, let, or qed.");

        this.compile(draft);
        this.draft = draft;
        return this.snapshot();
    }

    qed(name?: string) {
        if (this.recorded) return fail("This proof has already been recorded.");
        if (this.draft.pending.length) return fail("There are still open goals.");
        if (name !== undefined) {
            this.access?.checkCommand("m");
            this.system.checkDname(name);
            if (this.system.rules.has(name)) return fail(`Rule ${name} already exists.`);
        }
        const { scratch, proof } = this.compile(this.draft);
        if (!proof) return fail("There are still open goals.");
        const steps = scratch.props.slice();
        const macro = name === undefined ? undefined : scratch.m(name);
        const scope = this.system.saveContext().activeProp;
        for (const p of steps) this.access?.checkMove(p, scope, scratch);
        this.system.appendProof(steps, this.root.target);
        if (macro) this.system.rules.set(macro.name.name, macro);
        this.recorded = true;
        return macro;
    }

    private checkFresh(name: string, goal: Goal, variable = false) {
        if (!(variable ? variablePattern : namePattern).test(name)) fail("Invalid context name.");
        if (goal.bindings.has(name) || goal.variables.has(name)) fail(`Context name ${name} already exists.`);
    }

    private formula(text: string, goal?: Goal): AST {
        const ast = this.parser.parse(text, "wff");
        if (!ast || ast.end !== text.length) return fail("Expected one complete formula.");
        ast.checkWFF();
        ast.getReplvars();
        return reduceSubstitution(goal ? renameFreeItems(ast, goal.variables) : ast);
    }

    private source(text: string, goal: Goal, draft: Draft, apply: boolean) {
        const binding = goal.bindings.get(text);
        if (binding) return {
            source: { kind: "binding", id: binding.id } as Source, premises: [], conclusion: binding.formula,
        };
        if (goal.variables.has(text)) return fail(`${text} is a variable, not a proof.`);
        const cmd = this.parser.parse(`d ${text}`, "cmd");
        const [name, ...args] = cmd?.nodes ?? [];
        if (!name || cmd.end !== text.length + 2) return fail("Expected a context name or rule expression.");
        const scratch = this.scratch();
        this.access?.checkRuleName(name, scratch);
        const rule = scratch.getD(name);
        if (rule.error) return fail(`Rule ${name} has an invalid proof.`);
        const slots = new Map<string, AST>();
        const types = rule.conclusion.getReplvars();
        rule.conditions.forEach(p => p.getReplvars(types));
        for (const [key, item] of rule.replaceNames) types.set(key, item);
        for (const [key, item] of types) {
            slots.set(key, new AST(item ? NodeType.ATOM_ITEM : NodeType.ATOM_WFF, `${holePrefix}${goal.id}:${key.slice(1)}`));
        }
        const instance = (ast: AST) => ast.clone().mut_replaceByMatchTable(Object.fromEntries(slots));
        const premises = rule.conditions.map(instance);
        const inputs: Source[] = [];
        if (!apply) {
            if (args.length < premises.length) return fail("Pass each premise by its context name, or use apply.");
            premises.forEach((formula, i) => {
                const arg = args.shift()!;
                const premise = arg.isAtom() && goal.bindings.get(arg.name);
                if (!premise) return fail(`Unknown premise: ${arg}.`);
                unify(formula, premise.formula, draft.values);
                inputs.push({ kind: "binding", id: premise.id });
            });
        }
        if (args.length > rule.replaceNames.length) return fail("Too many rule arguments.");
        args.forEach((arg, i) => {
            const [key, item] = rule.replaceNames[i];
            const part = text.slice(arg.start! - 2, arg.end! - 2);
            const parsed = this.parser.parse(part, item ? "item" : "wff");
            if (!parsed || parsed.end !== part.length) return fail(`Invalid argument for ${key}.`);
            unify(slots.get(key)!, renameFreeItems(parsed, goal.variables), draft.values);
        });
        return {
            source: { kind: "rule", name, slots, inputs } as Source, premises: apply ? premises : [], conclusion: instance(rule.conclusion),
        };
    }

    private scratch() {
        const scratch = new HilbertSystem();
        scratch.rules = new Map(this.system.rules);
        scratch.renamedSysRule = new Map(this.system.renamedSysRule);
        return scratch;
    }

    private compile(draft: Draft) {
        const scratch = this.scratch();
        const references = new Map<number, Proposition>();
        const active = () => scratch.saveContext().activeProp;
        const inScope = (p: Proposition) => scratch.ref_addCaptureScopeToAST(p.ast, scratch.captureScope(active(), p));
        const rule = (name: AST): Deduction => {
            this.access?.checkRuleName(name, scratch);
            const d = scratch.getD(name);
            this.access?.checkScope(active(), d);
            return d;
        };
        const builtin = (name: string) => rule(new AST(NodeType.ATOM_DNAME, scratch.getSysRuleName(name)));
        const mp = (arrow: Proposition, premise: Proposition) => scratch.d(builtin("mp"), [arrow, premise], {});
        const materialize = (ast: AST): AST => {
            const result = resolve(ast, draft.values);
            if (hasHole(result)) return fail("An argument could not be inferred; supply it or prove a premise first.");
            return result;
        };
        const use = (source: Source, premises?: Proposition[]): Proposition => {
            if (source.kind === "binding") return references.get(source.id) ?? fail("Proof binding is not available here.");
            const d = rule(source.name);
            const replacements: MatchTable = Object.fromEntries(d.replaceNames.map(([key]) => {
                const slot = source.slots.get(key);
                if (!slot) return fail("The rule changed while the proof was open.");
                return [key, materialize(slot)];
            }));
            return scratch.d(d, premises ?? source.inputs.map(p => use(p)), replacements);
        };
        const finish = (p: Proposition) => {
            // A local proof may point outside this folder, or to an earlier
            // line. Reiterate only when necessary, using the base axioms.
            if (p.from.type === "d" && scratch.getLastChildP(active()) === p) return p;
            const ast = inScope(p);
            const a1 = builtin("a1");
            const table = new AST(NodeType.LOGIC, ">", ast, new AST(NodeType.LOGIC, ">", ast, ast))
                .match(a1.conclusion);
            return mp(mp(scratch.d(a1, [], table), p), p);
        };
        const visit = (goal: Goal): Proposition | undefined => {
            const action = draft.actions.get(goal.id);
            if (!action) return undefined;
            let proof: Proposition | undefined;
            switch (action.kind) {
                case "intro": {
                    this.access?.checkCommand(action.folder === "c" ? "cond" : "var");
                    const outer = active();
                    const ast = resolve(action.ast, draft.values);
                    if (hasHole(ast)) return undefined; // A premise can determine this in a later tactic.
                    const folder = scratch[action.folder](ast);
                    if (action.folder === "c") references.set(goal.id, folder);
                    const inner = visit(action.child);
                    if (inner) proof = finish(inner);
                    if (outer) scratch.cd(outer); else scratch.clearActiveDir();
                    break;
                }
                case "exact": proof = use(action.source); break;
                case "let":
                    references.set(goal.id, use(action.source));
                    proof = visit(action.next);
                    break;
                case "goal": {
                    const lemma = visit(action.lemma);
                    if (!lemma) return undefined;
                    references.set(action.lemma.id, lemma);
                    proof = visit(action.next);
                    break;
                }
                case "apply": {
                    const premises: Proposition[] = [];
                    for (const child of action.children) {
                        const p = visit(child);
                        if (!p) return undefined;
                        premises.push(p);
                    }
                    proof = action.useMp ? premises.reduce(mp, use(action.source)) : use(action.source, premises);
                    break;
                }
            }
            if (proof && !inScope(proof).equal(reduceSubstitution(materialize(goal.target)))) return fail("The checked proof does not match the goal.");
            return proof;
        };
        const result = visit(this.root);
        if (result) {
            const proof = finish(result);
            if (!inScope(proof).equal(this.root.target)) return fail("The checked proof does not match the original goal.");
            return { scratch, proof };
        }
        if (!draft.pending.length) fail("The proof has unresolved arguments.");
        return { scratch, proof: undefined };
    }
}
