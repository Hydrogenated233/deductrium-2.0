import assert from 'node:assert/strict';
import { test } from 'node:test';
import { SurvivalAccess } from '../js/hs/access.js';
import { HSLayer } from '../js/hs/main.js';
import { initialCreativeRules } from '../js/hs/core/initial.js';
import { HilbertSystem } from '../js/hs/core/core.js';
import { Deduction } from '../js/hs/core/deduction.js';
import { HSParser } from '../js/hs/core/parser.js';
import { AtomSolver } from '../js/hs/core/assert.js';
import { HilbertProofAssistant } from '../js/hs/proof-assistant.js';

const parse = (s, type = 'wff') => new HSParser().parse(s, type);
function fixture() {
    const hs = new HilbertSystem();
    for (const [name, header] of Object.entries({
        mp: '$1→$2,$1⊢$2', a1: '⊢$1→$2→$1', axeq: '⊢$x=$x',
        axchain: 'H⊢P→Q→R',
        axguard: '#nf($P,$x)⊢∀$x:$P', a4: '⊢(∀$x:$)→#sb($,$x,$A)',
    })) {
        const body = parse(header, 'rule');
        const assumes = body.nodes.slice(0, -1);
        const assertions = assumes.filter(n => n.name === 'nf').map(n => AtomSolver.fromAST(n));
        hs.rules.set(name, new Deduction(new Set(), parse(name, 'dname'), assertions,
            assumes.filter(n => n.name !== 'nf'), body.nodes.at(-1)));
    }
    return hs;
}
const run = (a, ...tactics) => tactics.forEach(t => a.execute(t));
const open = a => a.snapshot().goals.map(g => g.target);
const conclusion = hs => hs.checkConclusionInPropList().conclusion;
const assertionFailed = e => e?.type === 'deductFail' && e.cause?.type === 'assertFail';

test('named implication introduction, checked append, and macro expansion all preserve the target', () => {
    const hs = fixture();
    hs.fromCmd([parse('a1 P Q', 'cmd')]);
    const existing = hs.props[0];
    const a = new HilbertProofAssistant(hs, '$x→$x');
    run(a, 'intro h', 'exact h');
    assert.equal(hs.props.length, 1);
    assert.deepEqual(open(a), []);
    const macro = a.qed('sIdentity');
    assert.equal(hs.props[0], existing);
    assert.equal(macro.conditions.length, 0);
    assert.equal(macro.step.length, 1);
    assert.equal(macro.step[0].from.type, 'c');
    assert.equal(conclusion(hs).equal(parse('$x→$x')), true);
    assert.throws(() => a.qed(), /already been recorded/);
    hs.clear();
    hs.fromCmd([parse('sIdentity (P→Q)', 'cmd')]);
    hs.expand(hs.props[0]);
    assert.equal(conclusion(hs).equal(parse('(P→Q)→P→Q')), true);
    const saved = hs.genCmd();
    hs.clear();
    hs.fromCmd(saved.map(cmd => parse(cmd, 'cmd')));
    assert.equal(conclusion(hs).equal(parse('(P→Q)→P→Q')), true);
});

test('proof metavariables are rigid; fresh rule slots flow across premises independently', () => {
    const hs = fixture();
    const a = new HilbertProofAssistant(hs, '($x→$y)→$z→$x→$y');
    run(a, 'intro f', 'intro z', 'intro x', 'apply mp');
    assert.match(open(a)[0], /\?/);
    assert.match(open(a)[1], /\?/);
    run(a, 'exact f');
    assert.deepEqual(open(a), ['$x']);
    const before = a.snapshot();
    assert.throws(() => a.execute('exact z'), /does not match/);
    assert.deepEqual(a.snapshot(), before);
    run(a, 'exact x');
    a.qed();
    assert.equal(conclusion(hs).equal(parse('($x→$y)→$z→$x→$y')), true);
    const b = new HilbertProofAssistant(fixture(), '$x=$y');
    assert.throws(() => b.execute('exact axeq'), /does not match/);
});

test('successive applications of one rule do not share their schematic slots', () => {
    const hs = fixture();
    const target = '($x→$y)→($y→$z)→$x→$z';
    const a = new HilbertProofAssistant(hs, target);
    run(a, 'intro f', 'intro g', 'intro p', 'apply mp', 'exact g', 'apply mp', 'exact f');
    assert.deepEqual(open(a), ['$x']);
    run(a, 'exact p');
    a.qed();
    assert.equal(conclusion(hs).equal(parse(target)), true);
});

test('a context implication produces ordered premise goals, and exact can use a fully applied rule', () => {
    const hs = fixture();
    const a = new HilbertProofAssistant(hs, '(P→Q→R)→(P→Q)→P→R');
    run(a, 'intro f', 'intro g', 'intro p', 'apply f');
    assert.deepEqual(open(a), ['P', 'Q']);
    run(a, 'exact p', 'exact mp g p');
    a.qed();
    assert.equal(conclusion(hs).equal(parse('(P→Q→R)→(P→Q)→P→R')), true);
});

test('apply lists native rule premises before the needed implication antecedents', () => {
    for (const [target, goals, tactics] of [
        ['R', ['H', 'P', 'Q'], ['exact h', 'exact p', 'exact q']],
        ['Q→R', ['H', 'P'], ['exact h', 'exact p']],
        ['P→Q→R', ['H'], ['exact h']],
    ]) {
        const hs = fixture();
        const formula = `H→P→Q→(${target})`;
        const a = new HilbertProofAssistant(hs, formula);
        run(a, 'intro h', 'intro p', 'intro q', 'apply axchain');
        assert.deepEqual(open(a), goals);
        run(a, ...tactics);
        a.qed();
        assert.ok(conclusion(hs).equal(parse(formula)));
    }
});

test('apply discards slot assignments from a failed match before trying an implication tail', () => {
    const hs = fixture();
    const a = new HilbertProofAssistant(hs, 'P→Q→P');
    run(a, 'intro p', 'apply a1');
    assert.deepEqual(open(a), ['P']);
    run(a, 'exact p');
    a.qed();
    assert.ok(conclusion(hs).equal(parse('P→Q→P')));
});

test('let and auxiliary goal bind only their checked result in the resumed context', () => {
    const hs = fixture();
    const a = new HilbertProofAssistant(hs, 'P→Q→P');
    run(a, 'goal spare : R→R', 'intro h', 'exact h');
    assert.deepEqual(a.snapshot().goals[0].context.map(b => b.name), ['spare']);
    run(a, 'let alias := spare', 'let ax := a1 P Q', 'intro h', 'intro q', 'exact h');
    a.qed();
    assert.equal(hs.props.length, 3);
    assert.ok(hs.genCmd().includes('cd 0'));
    assert.equal(conclusion(hs).equal(parse('P→Q→P')), true);
});

test('universal intro aliases a native binder and rejects a capture in user input', () => {
    const hs = fixture();
    const a = new HilbertProofAssistant(hs, '∀$x:$x=$x');
    run(a, 'intro y');
    assert.deepEqual(open(a), ['y=y']);
    assert.throws(() => a.execute('goal captured : ∀$x:y=y'), /captured/);
    run(a, 'exact axeq y');
    a.qed();
    assert.equal(hs.props[0].ast.name, '$x');
    assert.equal(conclusion(hs).equal(parse('∀$x:$x=$x')), true);
});

test('rule conclusions match native substitutions after their slots are known', () => {
    const hs = fixture();
    const a = new HilbertProofAssistant(hs, '(∀x:x=x)→y=y');
    run(a, 'exact a4 x (x=x) y');
    a.qed();
    assert.equal(conclusion(hs).equal(parse('(∀x:x=x)→y=y')), true);
});

test('a specialized universal proof binds its reduced implication and can be applied', () => {
    const hs = fixture();
    const universal = parse('∀x:(x∈ℕ→S(x)∈ℕ)');
    hs.rules.set('apn2', new Deduction(new Set(), parse('apn2', 'dname'), [], [], universal));
    const a = new HilbertProofAssistant(hs, '0∈ℕ→S(0)∈ℕ');
    run(a, 'intro zero', 'let h := <a4(apn2) 0');
    assert.deepEqual(a.snapshot().goals[0].context.at(-1), { name: 'h', formula: '0∈ℕ→S(0)∈ℕ' });
    assert.deepEqual(a.recommendations(), ['apply h']);
    run(a, 'apply h', 'exact zero');
    a.qed();
    assert.equal(conclusion(hs).equal(parse('0∈ℕ→S(0)∈ℕ')), true);
});

test('kernel assertions are checked and failure leaves the current goal open', () => {
    const hs = fixture();
    const a = new HilbertProofAssistant(hs, '∀x:x=x');
    const before = a.snapshot();
    assert.throws(() => a.execute('exact axguard'), assertionFailed);
    assert.deepEqual(a.snapshot(), before);
    assert.equal(hs.props.length, 0);
    run(a, 'intro x', 'exact axeq');
    a.qed();
});

test('qed appends at the current insertion point and rolls back an incompatible append', () => {
    const hs = fixture();
    hs.fromCmd([parse('axeq $x', 'cmd'), parse('cond P', 'cmd')]);
    const [existing, folder] = hs.props;
    const a = new HilbertProofAssistant(hs, '$x→$x');
    run(a, 'goal aux : Q→Q', 'intro q', 'exact q', 'intro h', 'exact h');
    const before = hs.genCmd();
    assert.throws(() => a.qed('sBad'));
    assert.deepEqual(hs.genCmd(), before);
    assert.equal(hs.props[0], existing);
    assert.equal(hs.saveContext().activeProp, folder);
    assert.equal(folder.children.length, 0);
    assert.equal(hs.rules.has('sBad'), false);
    const b = new HilbertProofAssistant(hs, 'Q→Q');
    run(b, 'intro q', 'exact q');
    b.qed();
    assert.equal(hs.saveContext().activeProp, folder);
    assert.equal(conclusion(hs).equal(parse('P→Q→Q')), true);
});

test('the assistant respects cond/var/macro unlocks and accepts only complete input', () => {
    const hs = fixture();
    const access = new SurvivalAccess();
    const a = new HilbertProofAssistant(hs, 'P→P', access);
    assert.throws(() => a.execute('intro h'), e => e.type === 'lockedFeature');
    assert.throws(() => a.execute('goal aux : Q junk'), /complete formula/);
    assert.throws(() => a.execute('exact a1 P Q;clear'), /rule expression/);
    assert.throws(() => a.qed(), /open goals/);
    access.rewards.add('mct');
    run(a, 'intro h', 'exact h');
    assert.throws(() => a.qed('sID'), e => e.type === 'lockedFeature');
    assert.equal(hs.props.length, 0);
    a.qed();
});


test('recommendations are empty when nothing matches the goal', () => {
    const a = new HilbertProofAssistant(fixture(), '$x→$y');
    assert.deepEqual(a.recommendations(), ['intro h']);
    run(a, 'intro h');
    assert.deepEqual(a.recommendations(), []);
});

test('undo restores inferred slots and proof history after branching and an invalid command', () => {
    const a = new HilbertProofAssistant(fixture(), '($x→$y)→$x→$y');
    assert.deepEqual(a.recommendations(), ['intro h']);
    run(a, 'intro f', 'intro p', 'apply mp');
    const before = a.snapshot();
    assert.equal(before.history.at(-1).children.length, 2);
    run(a, 'exact f');
    assert.deepEqual(open(a), ['$x']);
    assert.throws(() => a.execute('exact f'), /does not match/);
    assert.equal(a.undo(), true);
    assert.deepEqual(a.snapshot(), before);
    run(a, 'exact f', 'exact p');
    assert.deepEqual(a.recommendations(), ['qed']);
    a.qed();
    assert.equal(a.undo(), false);
});

function creative() {
    const hs = new HilbertSystem();
    const layer = Object.assign(Object.create(HSLayer.prototype), { hilbertSystem: hs, ruleList: [] });
    layer.addRules(initialCreativeRules, { refresh: false });
    return hs;
}

test('apply can use the reduced implication of a specialized rule directly after rw', () => {
    const hs = creative();
    const target = '1∈ℕ';
    const a = new HilbertProofAssistant(hs, target);
    run(a, 'rw d1');
    assert.deepEqual(open(a), ['S(0)∈ℕ']);
    const before = a.snapshot();
    assert.throws(() => a.execute('exact <a4(apn2) 0'), /does not match/);
    assert.deepEqual(a.snapshot(), before);
    run(a, 'apply <a4(apn2) 0');
    assert.deepEqual(open(a), ['0∈ℕ']);
    run(a, 'exact apn1');
    a.qed('sOneNatural');
    assert.ok(conclusion(hs).equal(parse(target)));
    const commands = hs.genCmd();
    hs.clear();
    hs.fromCmd(commands.map(cmd => parse(cmd, 'cmd')));
    assert.ok(conclusion(hs).equal(parse(target)));
});

test('rw and rwb use the equality template to prove the original goal', () => {
    for (const [tactic, oldGoal, newGoal] of [
        ['rw h', 'a=a', 'b=b'], ['rw h #=a', 'a=a', 'b=a'],
        ['rwb h', 'b=b', 'a=a'], ['rwb h (b=#)', 'b=b', 'b=a'],
        ['rw h', '∀x∈a:x=x', '∀x∈b:x=x'],
    ]) {
        const hs = creative();
        const target = `a=b→(${newGoal})→(${oldGoal})`;
        const a = new HilbertProofAssistant(hs, target);
        run(a, 'intro h', 'intro p', tactic);
        assert.deepEqual(open(a), [parse(newGoal).toString()]);
        const rewrite = a.snapshot();
        assert.equal(a.undo(), true);
        assert.deepEqual(open(a), [parse(oldGoal).toString()]);
        run(a, tactic);
        assert.deepEqual(a.snapshot(), rewrite);
        run(a, 'exact p');
        a.qed('sRewrite');
        const commands = hs.genCmd();
        assert.ok(commands.some(cmd => cmd.startsWith('.a8<> ')));
        hs.clear();
        hs.fromCmd(commands.map(cmd => parse(cmd, 'cmd')));
        assert.ok(conclusion(hs).equal(parse(target)));
        hs.clear();
        hs.fromCmd([parse('sRewrite', 'cmd')]);
        hs.expand(hs.props[0]);
        assert.ok(conclusion(hs).equal(parse(target)));
    }
});

test('rw rejects invalid patterns and skips substitutions that would capture a variable', () => {
    const hs = creative();
    const a = new HilbertProofAssistant(hs, 'y=x→(∀x:y=x)∧y=y');
    run(a, 'intro h');
    const before = a.snapshot();
    for (const text of ['rw h #=z', 'rw h (∀x:#=x)∧y=y', 'rw h (∀x:y=x)∧y=y', 'rw h #=#;exact h']) {
        assert.throws(() => a.execute(text), undefined, text);
        assert.deepEqual(a.snapshot(), before);
    }
    run(a, 'rw h');
    assert.deepEqual(open(a), [parse('(∀x:y=x)∧x=x').toString()]);
    assert.deepEqual(hs.props, []);
});

test('biconditional rw records msbt in either direction and expands to the recorded goal', () => {
    for (const [tactic, oldGoal, newGoal, dname] of [
        ['rw h', 'P→P', 'Q→Q', 'msbt>'], ['rw h', 'P', 'Q', 'msbt>'],
        ['rwb h', 'Q→Q', 'P→P', 'msbt<'], ['rwb h #→Q', 'Q→Q', 'P→Q', 'msbt<'],
    ]) {
        const hs = creative();
        const target = `(P↔Q)→(${newGoal})→(${oldGoal})`;
        const a = new HilbertProofAssistant(hs, target);
        run(a, 'intro h', 'intro p', tactic);
        assert.deepEqual(open(a), [newGoal]);
        run(a, 'exact p');
        a.qed();
        const commands = hs.genCmd();
        assert.ok(commands.some(cmd => cmd.startsWith(dname + ' ')));
        hs.clear();
        hs.fromCmd(commands.map(cmd => parse(cmd, 'cmd')));
        const step = [...hs.flatProps.values()].find(p => p.from.data?.deduction?.name === dname);
        hs.expand(step);
        assert.ok(conclusion(hs).equal(parse(target)));
    }
});

test('reverse msbt expands formula and proof-step targets in the recorded direction', () => {
    const hs = creative();
    for (const [commands, expected] of [
        [['hyp P↔Q', 'hyp Q→Q', 'msbt< 1 2 0'], 'P→P'],
        [['msbt<(d\\/) (¬P→Q)→(¬P→Q) 0'], '((¬P→Q)→(¬P→Q))↔(P∨Q→P∨Q)'],
        [['hyp ¬P→Q', 'msbt<(d\\/) 1 0'], 'P∨Q'],
    ]) {
        hs.clear();
        hs.fromCmd(commands.map(cmd => parse(cmd, 'cmd')));
        const step = hs.props.at(-1);
        assert.ok(step.ast.equal(parse(expected)), commands.at(-1));
        hs.expand(step);
        assert.ok(hs.props.at(-1).ast.equal(parse(expected)), commands.at(-1));
    }
});

test('builtin .a8= lifts equality through an item template and expands without a new axiom', () => {
    const hs = creative();
    hs.fromCmd([parse('.a8= a b S(#) #', 'cmd')]);
    const expected = parse('a=b→S(a)=S(b)');
    assert.ok(hs.props[0].ast.equal(expected));
    hs.expand(hs.props[0]);
    assert.ok(conclusion(hs).equal(expected));
});
