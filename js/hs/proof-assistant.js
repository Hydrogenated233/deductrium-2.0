import { NodeType } from "../asttype.js";
import { Assertion, NFAssertion } from "./core/assert.js";
import { MSBT } from "./core/combine.js";
import { AST } from "./core/ast.js";
import { HilbertSystem } from "./core/core.js";
import { isHSErrorInfo } from "./core/error.js";
import { HSParser } from "./core/parser.js";
const namePattern = /^[a-z][A-Za-z0-9_]*$/;
const variablePattern = /^[$#]?[a-z][A-Za-z0-9_]*$/;
const holePrefix = "\0";
const isHole = (ast) => ast.name.startsWith(holePrefix);
const hasHole = (ast) => isHole(ast) || ast.nodes.some(hasHole);
const implication = (ast) => ast.type === NodeType.LOGIC && ast.name === ">";
const fail = (message) => { throw new Error(message); };
function resolve(ast, values) {
    const value = isHole(ast) ? values.get(ast.name) : undefined;
    return value ? resolve(value, values) : new AST(ast.type, ast.name, ...ast.nodes.map(n => resolve(n, values)));
}
// Native formulas (including every user-written $name) are rigid. Only nodes
// allocated while instantiating a rule participate in assistant unification.
function reduceSubstitution(ast) {
    if (!ast.hasSbFn())
        return ast;
    const reduced = ast.clone();
    Assertion.reduceSbFn([], reduced);
    return reduced;
}
function resolveFormula(ast, values) {
    // Work on a resolved copy. Leave unresolved or unsafe substitutions for
    // unification and kernel checking rather than guessing in a pending goal.
    const reduce = (node) => {
        if (node.type !== NodeType.SB) {
            node.nodes = node.nodes.map(reduce);
            return node;
        }
        if (hasHole(node))
            return node;
        try {
            return reduceSubstitution(node);
        }
        catch (error) {
            if (isHSErrorInfo(error) && error.type === "sbFail")
                return node;
            throw error;
        }
    };
    return reduce(resolve(ast, values));
}
function unify(left, right, values) {
    left = resolve(left, values);
    right = resolve(right, values);
    // Do not interpret uninstantiated rule slots as native variable names.
    if (left.type === NodeType.SB && !hasHole(left))
        left = reduceSubstitution(left);
    if (right.type === NodeType.SB && !hasHole(right))
        right = reduceSubstitution(right);
    const occurs = (name, term) => term.name === name || term.nodes.some(n => occurs(name, n));
    if (left.equal(right))
        return;
    if (!isHole(left) && isHole(right))
        return unify(right, left, values);
    if (isHole(left)) {
        if (occurs(left.name, right))
            fail("Circular rule argument.");
        if (isHole(right)) {
            if (left.type !== right.type)
                fail("Rule arguments have incompatible sorts.");
        }
        else if (left.type === NodeType.ATOM_ITEM)
            right.checkITEM();
        else
            right.checkWFF();
        values.set(left.name, right);
        return;
    }
    if (left.type !== right.type || left.name !== right.name || left.nodes.length !== right.nodes.length) {
        fail("The source does not match the goal or premise.");
    }
    for (let i = 0; i < left.nodes.length; i++)
        unify(left.nodes[i], right.nodes[i], values);
}
// Renaming applies to free occurrences only. Intro's alias is not a change to
// the kernel binder, and must not become captured when a formula is entered.
function renameFreeItems(ast, aliases, bound = new Set()) {
    if (ast.type === NodeType.ATOM_ITEM && !bound.has(ast.name)) {
        const name = aliases.get(ast.name);
        if (name !== undefined) {
            if (bound.has(name))
                fail(`Variable ${ast.name} would be captured by ${name}.`);
            return new AST(ast.type, name);
        }
    }
    const binder = ast.getBoundVarName();
    const body = ast.type === NodeType.RPL ? 0 : ast.type === NodeType.BOUNDED_QUANT || ast.type === NodeType.SEP ? 2 : 1;
    const binderIndex = ast.type === NodeType.RPL ? 1 : 0;
    return new AST(ast.type, ast.name, ...ast.nodes.map((n, i) => {
        if (binder === undefined)
            return renameFreeItems(n, aliases, bound);
        if (i === binderIndex)
            return n.clone();
        return renameFreeItems(n, aliases, i === body ? new Set([...bound, binder]) : bound);
    }));
}
// Build the formula template without abstracting bound occurrences or
// creating a substitution that would capture a variable on either side.
function equalityFrame(target, from, to, hole, system) {
    const asserts = system.getAsserts();
    const visit = (node, bound) => {
        if (node.equal(from) && [from, to].every(term => Assertion.check(asserts, new NFAssertion(term, bound, new Set()).reduce()).passed))
            return hole.clone();
        if (node.type === NodeType.SB)
            return node.clone(); // Opaque, still-schematic substitution.
        const binder = node.getBoundVarName();
        const declaration = node.type === NodeType.RPL ? 1 : 0;
        const body = node.type === NodeType.RPL ? 0 : node.type === NodeType.SEP || node.type === NodeType.BOUNDED_QUANT ? 2 : 1;
        return new AST(node.type, node.name, ...node.nodes.map((child, i) => {
            if (binder === undefined)
                return visit(child, bound);
            if (i === declaration)
                return child.clone();
            return visit(child, i === body ? new Set([...bound, binder]) : bound);
        }));
    };
    return visit(target, new Set());
}
// A biconditional pattern selects positions, not a new proof rule. Translate
// its holes into the ordinary exact-match MSBT indices.
function rewriteIndices(system, relation, reverse, target, pattern) {
    const from = relation.nodes[reverse ? 1 : 0];
    const search = new MSBT(system, relation, true, target, true, !reverse);
    search.searchIter(from, target, []);
    const selected = [];
    const visit = (frame, old, pos) => {
        if (frame.isAtom() === "#") {
            const i = search.absPosRes.findIndex(p => MSBT.eq(p, pos));
            if (i < 0)
                return fail("A rewrite placeholder does not match an eligible occurrence.");
            selected.push(new AST(NodeType.ATOM_ITEM, String(i + 1)));
            return;
        }
        if (frame.type !== old.type || frame.name !== old.name || frame.nodes.length !== old.nodes.length) {
            return fail("The rewrite pattern does not reconstruct the current goal.");
        }
        frame.nodes.forEach((child, i) => visit(child, old.nodes[i], [...pos, i]));
    };
    visit(pattern, target, []);
    if (!selected.length)
        return fail("The rewrite pattern needs a # placeholder.");
    return new AST(NodeType.FN, "{}", ...selected);
}
export class HilbertProofAssistant {
    system;
    access;
    parser = new HSParser();
    root;
    draft;
    recorded = false;
    history = [];
    constructor(system, target, access) {
        this.system = system;
        this.access = access;
        const ast = this.formula(target.trim());
        this.root = { id: 0, target: ast, bindings: new Map(), variables: new Map() };
        this.draft = this.initialDraft();
    }
    initialDraft() {
        return { pending: [this.root], actions: new Map(), values: new Map(), nextId: 1 };
    }
    snapshot() {
        const show = (ast, goal) => {
            const resolved = resolveFormula(ast, this.draft.values);
            const aliases = new Map([...goal.variables].map(([alias, binder]) => [binder, alias]));
            let displayed;
            try {
                displayed = renameFreeItems(resolved, aliases);
            }
            catch {
                displayed = resolved;
            }
            const simplifyHoles = (a) => {
                if (isHole(a))
                    a.name = `?${a.name.slice(holePrefix.length).replace(":", "_")}`;
                a.nodes.forEach(simplifyHoles);
            };
            simplifyHoles(displayed);
            return displayed.toString();
        };
        return {
            target: this.root.target.toString(),
            history: this.history.map(({ goal, text }) => {
                const action = this.draft.actions.get(goal);
                const children = action.kind === "goal" ? [action.lemma, action.next]
                    : action.kind === "apply" ? action.children
                        : action.kind === "intro" || action.kind === "rewrite" ? [action.child]
                            : action.kind === "let" ? [action.next] : [];
                return { goal, text, children: children.map(child => child.id) };
            }),
            goals: this.draft.pending.map(goal => ({
                id: goal.id,
                target: show(goal.target, goal),
                context: [...goal.variables].map(([name]) => ({ name, formula: null }))
                    .concat([...goal.bindings].map(([name, binding]) => ({ name, formula: show(binding.formula, goal) }))),
            })),
        };
    }
    undo() {
        if (this.recorded || !this.history.length)
            return false;
        const prefix = this.history.slice(0, -1);
        // Replay before publishing so even a rule changed elsewhere cannot
        // leave this draft in a partially reverted state.
        const draft = prefix.reduce((state, { text }) => this.executeDraft(text, state), this.initialDraft());
        this.history.pop();
        this.draft = draft;
        return true;
    }
    recommendations() {
        const [goal] = this.draft.pending;
        if (!goal)
            return ["qed"];
        const target = resolveFormula(goal.target, this.draft.values);
        const isUniversal = target.type === NodeType.QUANT && target.name === "\\a";
        const suggestions = [];
        if (implication(target) || isUniversal) {
            try {
                this.access?.checkCommand(isUniversal ? "var" : "cond");
                const base = isUniversal ? target.nodes[0].name : "h";
                if (!isUniversal || (variablePattern.test(base) && ![...goal.variables.values()].includes(base)
                    && !goal.variables.has(base) && !goal.bindings.has(base))) {
                    let name = base;
                    for (let i = 1; goal.variables.has(name) || goal.bindings.has(name); i++)
                        name = base + i;
                    suggestions.push(`intro ${name}`);
                }
            }
            catch { /* The corresponding introduction is not unlocked. */ }
        }
        for (const [name, binding] of goal.bindings) {
            let candidate = resolveFormula(binding.formula, this.draft.values);
            let tactic = "exact";
            while (true) {
                try {
                    unify(target, candidate, new Map(this.draft.values));
                    suggestions.push(`${tactic} ${name}`);
                    break;
                }
                catch {
                    if (!implication(candidate))
                        break;
                    candidate = candidate.nodes[1];
                    tactic = "apply";
                }
            }
        }
        return suggestions;
    }
    execute(text) {
        if (this.recorded)
            return fail("This proof has already been recorded.");
        const goal = this.draft.pending[0]?.id;
        this.draft = this.executeDraft(text, this.draft);
        this.history.push({ goal: goal, text: text.trim() });
        return this.snapshot();
    }
    executeDraft(text, previous) {
        const [, command, argument = ""] = /^([a-z]+)(?:\s+([^\r\n]*))?$/.exec(text.trim()) ?? [];
        const [current, ...remaining] = previous.pending;
        if (!current)
            return fail("The proof is complete. Use qed to record it.");
        const draft = {
            pending: remaining, actions: new Map(previous.actions),
            values: new Map(previous.values), nextId: previous.nextId,
        };
        const target = resolveFormula(current.target, draft.values);
        const subgoal = (formula, bindings = current.bindings, variables = current.variables) => ({ id: draft.nextId++, target: formula, bindings, variables });
        const withBinding = (name, id, formula) => new Map([...current.bindings, [name, { id, formula }]]);
        const set = (action, ...next) => {
            draft.actions.set(current.id, action);
            draft.pending.unshift(...next);
        };
        if (command === "intro") {
            if (implication(target)) {
                this.checkFresh(argument, current);
                const child = subgoal(target.nodes[1], withBinding(argument, current.id, target.nodes[0]));
                set({ kind: "intro", folder: "c", ast: target.nodes[0], child }, child);
            }
            else if (target.type === NodeType.QUANT && target.name === "\\a") {
                this.checkFresh(argument, current, true);
                const binder = target.nodes[0];
                if (hasHole(binder))
                    return fail("The quantified variable must be determined before intro.");
                if ([...current.variables.values()].includes(binder.name))
                    return fail("Rename the shadowed quantifier before intro.");
                const mentions = (node) => node.name === argument || node.nodes.some(mentions);
                if (argument !== binder.name && (mentions(target) || [...current.bindings.values()].some(b => mentions(b.formula))
                    || [...current.variables.values()].includes(argument)))
                    return fail("Choose a fresh variable name.");
                const child = subgoal(target.nodes[1], current.bindings, new Map([...current.variables, [argument, binder.name]]));
                set({ kind: "intro", folder: "v", ast: binder, child }, child);
            }
            else
                return fail("Intro requires an implication or a universal quantifier.");
        }
        else if (command === "goal") {
            const match = /^(\S+)\s*:\s*(.+)$/.exec(argument);
            if (!match)
                return fail("Use goal name : formula.");
            const [, name, text] = match;
            this.checkFresh(name, current);
            const lemma = subgoal(this.formula(text, current));
            const next = subgoal(current.target, withBinding(name, lemma.id, lemma.target));
            set({ kind: "goal", lemma, next }, lemma, next);
        }
        else if (command === "let") {
            const match = /^(\S+)\s*:=\s*(.+)$/.exec(argument);
            if (!match)
                return fail("Use let name := source.");
            const [, name, text] = match;
            this.checkFresh(name, current);
            const expression = this.source(text, current, draft, false);
            const next = subgoal(current.target, withBinding(name, current.id, expression.conclusion));
            set({ kind: "let", source: expression.source, next }, next);
        }
        else if (command === "exact" || command === "apply") {
            const expression = this.source(argument, current, draft, command === "apply");
            if (command === "exact") {
                unify(target, expression.conclusion, draft.values);
                set({ kind: "exact", source: expression.source });
            }
            else {
                const premises = expression.premises.slice();
                let conclusion = resolveFormula(expression.conclusion, draft.values);
                // Prefer the whole conclusion, then successively consume
                // antecedents. A failed trial must not constrain the next one.
                while (true) {
                    const trial = new Map(draft.values);
                    try {
                        unify(target, conclusion, trial);
                    }
                    catch (error) {
                        if (!implication(conclusion))
                            throw error;
                        premises.push(conclusion.nodes[0]);
                        conclusion = conclusion.nodes[1];
                        continue;
                    }
                    draft.values = trial;
                    break;
                }
                const children = premises.map(ast => subgoal(ast));
                set({ kind: "apply", source: expression.source, children, rulePremiseCount: expression.premises.length }, ...children);
            }
        }
        else if (command === "rw" || command === "rwb") {
            const [, name, pattern] = /^(\S+)(?:\s+(.+))?$/.exec(argument) ?? [];
            if (!name)
                return fail(`Use ${command} h [pattern].`);
            const { source } = this.source(name, current, draft, false);
            const rewrite = { source, reverse: command === "rwb", pattern: pattern ?
                    renameFreeItems(this.parseFormula(pattern), current.variables) : undefined };
            // Visit the focused goal in the same scope as qed; the kernel
            // produces the implication before we publish the new goal.
            const { rewriteTarget } = this.compile(draft, { id: current.id, rewrite });
            if (!rewriteTarget)
                return fail("The rewrite needs its proof and goal to be determined.");
            const child = subgoal(rewriteTarget);
            set({ kind: "rewrite", rewrite, child }, child);
            return draft;
        }
        else
            return fail("Use intro, exact, apply, rw, rwb, goal, let, or qed.");
        this.compile(draft);
        return draft;
    }
    qed(name) {
        if (this.recorded)
            return fail("This proof has already been recorded.");
        if (this.draft.pending.length)
            return fail("There are still open goals.");
        if (name !== undefined) {
            this.access?.checkCommand("m");
            this.system.checkDname(name);
            if (this.system.rules.has(name))
                return fail(`Rule ${name} already exists.`);
        }
        const { scratch, proof } = this.compile(this.draft);
        if (!proof)
            return fail("There are still open goals.");
        const steps = scratch.props.slice();
        const macro = name === undefined ? undefined : scratch.m(name);
        const scope = this.system.saveContext().activeProp;
        for (const p of steps)
            this.access?.checkMove(p, scope, scratch);
        this.system.appendProof(steps, this.root.target);
        if (macro)
            this.system.rules.set(macro.name.name, macro);
        this.recorded = true;
        return macro;
    }
    checkFresh(name, goal, variable = false) {
        if (!(variable ? variablePattern : namePattern).test(name))
            fail("Invalid context name.");
        if (goal.bindings.has(name) || goal.variables.has(name))
            fail(`Context name ${name} already exists.`);
    }
    parseFormula(text) {
        const ast = this.parser.parse(text, "wff");
        if (!ast || ast.end !== text.length)
            return fail("Expected one complete formula.");
        return ast;
    }
    formula(text, goal) {
        const ast = this.parseFormula(text);
        ast.checkWFF();
        ast.getReplvars();
        return reduceSubstitution(goal ? renameFreeItems(ast, goal.variables) : ast);
    }
    source(text, goal, draft, apply) {
        const binding = goal.bindings.get(text);
        if (binding)
            return {
                source: { kind: "binding", id: binding.id }, premises: [], conclusion: binding.formula,
            };
        if (goal.variables.has(text))
            return fail(`${text} is a variable, not a proof.`);
        const cmd = this.parser.parse(`d ${text}`, "cmd");
        const [name, ...args] = cmd?.nodes ?? [];
        if (!name || cmd.end !== text.length + 2)
            return fail("Expected a context name or rule expression.");
        const scratch = this.scratch();
        this.access?.checkRuleName(name, scratch);
        const rule = scratch.getD(name);
        if (rule.error)
            return fail(`Rule ${name} has an invalid proof.`);
        const slots = new Map();
        const types = rule.conclusion.getReplvars();
        rule.conditions.forEach(p => p.getReplvars(types));
        for (const [key, item] of rule.replaceNames)
            types.set(key, item);
        for (const [key, item] of types) {
            slots.set(key, new AST(item ? NodeType.ATOM_ITEM : NodeType.ATOM_WFF, `${holePrefix}${goal.id}:${key.slice(1)}`));
        }
        const instance = (ast) => ast.clone().mut_replaceByMatchTable(Object.fromEntries(slots));
        const premises = rule.conditions.map(instance);
        const inputs = [];
        if (!apply) {
            if (args.length < premises.length)
                return fail("Pass each premise by its context name, or use apply.");
            premises.forEach((formula, i) => {
                const arg = args.shift();
                const premise = arg.isAtom() && goal.bindings.get(arg.name);
                if (!premise)
                    return fail(`Unknown premise: ${arg}.`);
                unify(formula, premise.formula, draft.values);
                inputs.push({ kind: "binding", id: premise.id });
            });
        }
        if (args.length > rule.replaceNames.length)
            return fail("Too many rule arguments.");
        args.forEach((arg, i) => {
            const [key, item] = rule.replaceNames[i];
            const part = text.slice(arg.start - 2, arg.end - 2);
            const parsed = this.parser.parse(part, item ? "item" : "wff");
            if (!parsed || parsed.end !== part.length)
                return fail(`Invalid argument for ${key}.`);
            unify(slots.get(key), renameFreeItems(parsed, goal.variables), draft.values);
        });
        return {
            source: { kind: "rule", name, slots, inputs }, premises: apply ? premises : [], conclusion: instance(rule.conclusion),
        };
    }
    scratch() {
        const scratch = new HilbertSystem();
        scratch.rules = new Map(this.system.rules);
        scratch.renamedSysRule = new Map(this.system.renamedSysRule);
        return scratch;
    }
    compile(draft, probe) {
        const scratch = this.scratch();
        const references = new Map();
        const active = () => scratch.saveContext().activeProp;
        const inScope = (p) => scratch.ref_addCaptureScopeToAST(p.ast, scratch.captureScope(active(), p));
        const rule = (name) => {
            this.access?.checkRuleName(name, scratch);
            const d = scratch.getD(name);
            this.access?.checkScope(active(), d);
            return d;
        };
        const builtin = (name) => rule(new AST(NodeType.ATOM_DNAME, scratch.getSysRuleName(name)));
        const mp = (arrow, premise) => scratch.d(builtin("mp"), [arrow, premise], {});
        const materialize = (ast) => {
            const result = resolve(ast, draft.values);
            if (hasHole(result))
                return fail("An argument could not be inferred; supply it or prove a premise first.");
            return result;
        };
        const use = (source, premises) => {
            if (source.kind === "binding")
                return references.get(source.id) ?? fail("Proof binding is not available here.");
            const d = rule(source.name);
            const replacements = Object.fromEntries(d.replaceNames.map(([key]) => {
                const slot = source.slots.get(key);
                if (!slot)
                    return fail("The rule changed while the proof was open.");
                return [key, materialize(slot)];
            }));
            return scratch.d(d, premises ?? source.inputs.map(p => use(p)), replacements);
        };
        const rewriteArrow = (goal, { source, reverse, pattern }) => {
            const target = reduceSubstitution(materialize(goal.target));
            const proof = use(source);
            const relation = inScope(proof);
            const direction = (iff, backward = false) => {
                const [left, right] = inScope(iff).nodes;
                return mp(scratch.d(builtin(backward ? ".<>1" : ".<>2"), [], { $1: left, $2: right }), iff);
            };
            let arrow;
            if (relation.type === NodeType.PRED && relation.name === "=") {
                const [left, right] = relation.nodes;
                const [from, to] = reverse ? [right, left] : [left, right];
                const used = target.getLocalvars(relation.getLocalvars());
                pattern?.getLocalvars(used);
                let name = "#";
                for (let i = 0; used.has(name); i++)
                    name = "#" + i;
                const marker = new AST(NodeType.ATOM_ITEM, name);
                const frame = pattern ? pattern.clone().renameLocalVars_mut(new Map([["#", name]]))
                    : equalityFrame(target, from, to, marker, scratch);
                if (!frame.getLocalvars().has(name))
                    return fail(pattern ?
                        "The rewrite pattern needs a # placeholder." : "No eligible occurrence to rewrite.");
                const congruence = scratch.d(builtin(".a8<>"), [], { $1: left, $2: right, $3: frame, $0: marker });
                arrow = direction(mp(congruence, proof), reverse);
            }
            else if (relation.type === NodeType.LOGIC && relation.name === "<>") {
                const name = new AST(NodeType.ATOM_DNAME, reverse ? "msbt<" : "msbt>");
                this.access?.checkRuleName(name, scratch);
                this.access?.checkScope(active());
                if (!relation.equal(proof.ast))
                    return fail("The equivalence is not available in this scope.");
                const indices = pattern ? rewriteIndices(scratch, relation, reverse, target, pattern)
                    : new AST(NodeType.ATOM_ITEM, "0");
                const iff = scratch.msbt([name, new AST(NodeType.ATOM_ITEM, String(proof.id)), target, indices]);
                arrow = direction(iff);
            }
            else
                return fail("Rewrite needs a proof of an equality or equivalence.");
            const formula = inScope(arrow);
            if (!implication(formula) || !formula.nodes[1].equal(target)) {
                return fail("The rewrite pattern does not reconstruct the current goal.");
            }
            return { arrow, target: formula.nodes[0] };
        };
        const finish = (p) => {
            // A local proof may point outside this folder, or to an earlier
            // line. Reiterate only when necessary, using the base axioms.
            if (p.from.type === "d" && scratch.getLastChildP(active()) === p)
                return p;
            const ast = inScope(p);
            const a1 = builtin("a1");
            const table = new AST(NodeType.LOGIC, ">", ast, new AST(NodeType.LOGIC, ">", ast, ast))
                .match(a1.conclusion);
            return mp(mp(scratch.d(a1, [], table), p), p);
        };
        let rewriteTarget;
        const visit = (goal) => {
            const action = draft.actions.get(goal.id);
            if (!action) {
                if (probe?.id === goal.id)
                    rewriteTarget = rewriteArrow(goal, probe.rewrite).target;
                return undefined;
            }
            let proof;
            switch (action.kind) {
                case "intro": {
                    this.access?.checkCommand(action.folder === "c" ? "cond" : "var");
                    const outer = active();
                    const ast = resolve(action.ast, draft.values);
                    if (hasHole(ast))
                        return undefined; // A premise can determine this in a later tactic.
                    const folder = scratch[action.folder](ast);
                    if (action.folder === "c")
                        references.set(goal.id, folder);
                    const inner = visit(action.child);
                    if (inner)
                        proof = finish(inner);
                    if (outer)
                        scratch.cd(outer);
                    else
                        scratch.clearActiveDir();
                    break;
                }
                case "exact":
                    proof = use(action.source);
                    break;
                case "let":
                    references.set(goal.id, use(action.source));
                    proof = visit(action.next);
                    break;
                case "goal": {
                    const lemma = visit(action.lemma);
                    if (!lemma)
                        return undefined;
                    references.set(action.lemma.id, lemma);
                    proof = visit(action.next);
                    break;
                }
                case "rewrite": {
                    const { arrow } = rewriteArrow(goal, action.rewrite);
                    const premise = visit(action.child);
                    if (premise)
                        proof = mp(arrow, premise);
                    break;
                }
                case "apply": {
                    const premises = [];
                    for (const child of action.children) {
                        const p = visit(child);
                        if (!p)
                            return undefined;
                        premises.push(p);
                    }
                    const result = use(action.source, premises.slice(0, action.rulePremiseCount));
                    proof = premises.slice(action.rulePremiseCount).reduce(mp, result);
                    break;
                }
            }
            if (proof && !inScope(proof).equal(reduceSubstitution(materialize(goal.target))))
                return fail("The checked proof does not match the goal.");
            return proof;
        };
        const result = visit(this.root);
        if (result) {
            const proof = finish(result);
            if (!inScope(proof).equal(this.root.target))
                return fail("The checked proof does not match the original goal.");
            return { scratch, proof, rewriteTarget };
        }
        if (!probe && !draft.pending.length)
            fail("The proof has unresolved arguments.");
        return { scratch, proof: undefined, rewriteTarget };
    }
}
//# sourceMappingURL=proof-assistant.js.map