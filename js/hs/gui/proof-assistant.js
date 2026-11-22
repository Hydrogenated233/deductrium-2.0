import { SyntaxEditor, SyntaxViewer } from "../../astrender.js";
import { LangMgr } from "../../lang.js";
import { isHSErrorInfo } from "../core/error.js";
import { HSParser } from "../core/parser.js";
import { HilbertProofAssistant } from "../proof-assistant.js";
// Keep tactic keywords and names literal. Formula and rule operands use the
// same tokenizer, symbol replacements and binding highlights as the command bar.
class ProofInputParser {
    boundNames;
    hs = new HSParser();
    tokens = [];
    inputReplacements = this.hs.inputReplacements;
    allowReplaceTokenType = this.hs.allowReplaceTokenType;
    constructor(boundNames) {
        this.boundNames = boundNames;
    }
    getTokens() { return this.tokens; }
    parse(text, mode) {
        const literal = (start, end, type = "cmd-atom-param") => {
            if (end <= start)
                return;
            const value = text.slice(start, end);
            this.tokens.push({ type, text: value, displayText: value, start, end });
        };
        const operand = (offset, type, limit = text.length) => {
            if (offset >= limit)
                return null;
            const prefix = type === "cmd" ? " ".repeat(offset - 2) + "d " : " ".repeat(offset);
            const parsed = this.hs.parse(prefix + text.slice(offset, limit), type);
            let end = offset;
            for (const token of this.hs.getTokens()) {
                if (token.start < offset)
                    continue;
                literal(end, token.start);
                // Opened quantifiers still bind these item variables in the proof context.
                const bound = this.boundNames?.has(token.text) &&
                    ["atom-free-var", "atom-locvar", "replvar-item", "replvar-var"].includes(token.type);
                this.tokens.push(bound ? { ...token, type: "atom-var" } : token);
                end = token.end;
            }
            // Formula tokenization stops at a command separator. Keep the
            // unparsed suffix visible and let the checker reject it on submit.
            literal(end, limit);
            return parsed;
        };
        this.tokens = [];
        if (mode === "wff")
            return operand(0, "wff");
        const head = /^(\s*)(intro|hyp|exact|apply|rw|rwb|goal|let|qed)(?=\s|$)(\s*)/.exec(text);
        if (!head) {
            literal(0, text.length);
            return null;
        }
        const [, leading, command] = head;
        literal(0, leading.length, "space");
        literal(leading.length, leading.length + command.length, "cmd");
        literal(leading.length + command.length, head[0].length, "space");
        let offset = head[0].length;
        if (command === "goal" || command === "hyp" || command === "let") {
            const separator = command === "let" ? /^\S+?\s*:=\s*/ : /^[^\s:]+\s*:\s*/;
            const name = separator.exec(text.slice(offset));
            if (!name) {
                literal(offset, text.length);
                return null;
            }
            literal(offset, offset + name[0].length);
            offset += name[0].length;
            return operand(offset, command === "let" ? "cmd" : "wff");
        }
        if (command === "exact" || command === "apply" || command === "rw" || command === "rwb") {
            return operand(offset, "cmd");
        }
        literal(offset, text.length, mode === "quantifier-intro" && command === "intro" ? "atom-var" : "cmd-atom-param");
        return null;
    }
}
function editor(mount, mode, id) {
    const view = new SyntaxEditor(mount, new ProofInputParser(), "", mode);
    view.singleLine = true;
    view.input.id = id;
    view.input.rows = 1;
    view.input.enterKeyHint = "go";
    view.input.setAttribute("aria-labelledby", "hs-assistant-label");
    return view;
}
function syntax(text, mode, boundNames) {
    const span = document.createElement("span");
    new SyntaxViewer(span, new ProofInputParser(boundNames), text, mode);
    return span;
}
export class ProofAssistantPanel {
    sheet;
    drafts = new WeakMap();
    label;
    target;
    tactic;
    draft;
    history;
    goals;
    cancel;
    undo;
    status;
    recommendations;
    recommendationButtons;
    wrapper;
    targetMount;
    tacticMount;
    constructor(panel, system, sheet, access, canEdit, record) {
        this.sheet = sheet;
        const get = (id) => panel.querySelector(`#hs-assistant-${id}`);
        const form = get("form");
        this.label = get("label");
        this.targetMount = get("target-editor");
        this.tacticMount = get("tactic-editor");
        this.target = editor(this.targetMount, "wff", "hs-assistant-target");
        this.tactic = editor(this.tacticMount, "tactic", "hs-assistant-tactic");
        this.draft = get("draft");
        this.history = get("history");
        this.goals = get("goals");
        this.status = get("status");
        this.cancel = get("cancel");
        this.undo = get("undo");
        this.recommendations = get("recommendations");
        this.recommendationButtons = get("recommendation-buttons");
        this.wrapper = panel.querySelector(".hs-assistant-wrapper");
        this.target.onEnter = this.tactic.onEnter = () => form.requestSubmit();
        form.addEventListener("submit", event => {
            event.preventDefault();
            const key = sheet();
            if (!key || !canEdit())
                return;
            const assistant = this.drafts.get(key);
            const text = (assistant ? this.tactic : this.target).getValue().trim();
            if (!text)
                return;
            this.run(() => {
                if (!assistant) {
                    this.drafts.set(key, new HilbertProofAssistant(system, text, access()));
                    this.target.setValue("");
                }
                else {
                    const qed = /^qed(?:\s+(.+))?$/.exec(text);
                    if (qed) {
                        const macro = assistant.qed(qed[1]);
                        this.drafts.delete(key);
                        record(macro?.name.name);
                    }
                    else
                        assistant.execute(text);
                    this.tactic.setValue("");
                }
                this.render(true);
            });
        });
        this.undo.addEventListener("click", () => {
            const key = sheet();
            if (!key)
                return;
            this.run(() => {
                if (!this.drafts.get(key)?.undo())
                    this.drafts.delete(key);
                this.tactic.setValue("");
                this.render(true);
            });
        });
        this.cancel.addEventListener("click", () => {
            const key = sheet();
            if (key)
                this.drafts.delete(key);
            this.showSheet();
            this.target.focus();
        });
        this.recommendationButtons.addEventListener("click", event => {
            if (!(event.target instanceof HTMLButtonElement))
                return;
            this.tactic.setValue(event.target.textContent ?? "");
            form.requestSubmit();
        });
        this.render();
    }
    reset() {
        this.drafts = new WeakMap();
        this.showSheet();
    }
    showSheet() {
        this.target.setValue("");
        this.tactic.setValue("");
        this.message("");
        this.render();
    }
    run(operation) {
        this.message("");
        try {
            operation();
        }
        catch (error) {
            this.message(isHSErrorInfo(error) ? LangMgr.renderHSError(error)
                : error instanceof Error ? error.message : String(error));
            (this.tacticMount.hidden ? this.target : this.tactic).focus();
        }
        this.wrapper.scrollTop = this.wrapper.scrollHeight;
    }
    message(text) {
        this.status.textContent = text;
        this.status.hidden = !text;
    }
    render(focus = false) {
        const key = this.sheet();
        const assistant = key && this.drafts.get(key);
        this.label.htmlFor = (assistant ? this.tactic : this.target).input.id;
        this.targetMount.hidden = !!assistant;
        this.tacticMount.hidden = !assistant;
        this.draft.hidden = this.cancel.hidden = this.undo.hidden = !assistant;
        this.history.replaceChildren();
        this.goals.replaceChildren();
        this.recommendationButtons.replaceChildren();
        this.recommendations.hidden = true;
        if (focus)
            (assistant ? this.tactic : this.target).focus();
        if (!assistant)
            return;
        const state = assistant.snapshot();
        for (const { text, quantifierIntro } of state.history) {
            const line = document.createElement("div");
            line.append(syntax(text, quantifierIntro ? "quantifier-intro" : "tactic"), " . ");
            this.history.append(line);
        }
        const localized = (key) => {
            const span = document.createElement("span");
            span.dataset.i18n = key;
            span.textContent = LangMgr.text[key];
            return span;
        };
        if (!state.goals.length)
            this.goals.append(localized("hsAssistantReady"));
        for (let i = state.goals.length - 1; i >= 0; i--) {
            const { context, target } = state.goals[i];
            const boundNames = new Set(context.filter(entry => entry.formula === null).map(entry => entry.name));
            const line = document.createElement("div");
            line.className = i ? "hs-assistant-goal-pending" : "hs-assistant-goal-current";
            for (const { name, formula } of [...context].reverse()) {
                if (formula === null) {
                    const variable = document.createElement("span");
                    variable.className = "token-atom-var";
                    variable.textContent = name;
                    line.append(variable);
                }
                else {
                    line.append(syntax(name, "wff"), " : ", syntax(formula, "wff", boundNames));
                }
                line.append(document.createElement("br"));
            }
            line.append(document.createElement("br"));
            line.append(localized(i ? "hsAssistantGoal" : "hsAssistantCurrent"));
            if (i)
                line.append(`${i}：`);
            line.append(syntax(target, "wff", boundNames));
            this.goals.append(document.createElement("hr"), line);
        }
        for (const text of assistant.recommendations()) {
            const button = document.createElement("button");
            button.type = "button";
            button.textContent = text;
            this.recommendationButtons.append(button);
        }
        this.recommendations.hidden = !this.recommendationButtons.childElementCount;
    }
}
//# sourceMappingURL=proof-assistant.js.map