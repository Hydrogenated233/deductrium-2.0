import { SyntaxEditor, SyntaxViewer, type IParser, type Token } from "../../astrender.js";
import { LangMgr } from "../../lang.js";
import type { SurvivalAccess } from "../access.js";
import type { HilbertSystem } from "../core/core.js";
import { isHSErrorInfo } from "../core/error.js";
import { HSParser } from "../core/parser.js";
import { HilbertProofAssistant } from "../proof-assistant.js";

type InputMode = "wff" | "tactic";

// Keep tactic keywords and names literal. Formula and rule operands use the
// same tokenizer, symbol replacements and binding highlights as the command bar.
class ProofInputParser implements IParser {
    private readonly hs = new HSParser();
    private tokens: Token[] = [];
    readonly inputReplacements = this.hs.inputReplacements;
    allowReplaceTokenType = this.hs.allowReplaceTokenType;
    getTokens() { return this.tokens; }

    parse(text: string, mode: InputMode) {
        const literal = (start: number, end: number, type = "cmd-atom-param") => {
            if (end <= start) return;
            const value = text.slice(start, end);
            this.tokens.push({ type, text: value, displayText: value, start, end });
        };
        const operand = (offset: number, type: "wff" | "cmd", limit = text.length) => {
            if (offset >= limit) return null;
            const prefix = type === "cmd" ? " ".repeat(offset - 2) + "d " : " ".repeat(offset);
            const parsed = this.hs.parse(prefix + text.slice(offset, limit), type);
            let end = offset;
            for (const token of this.hs.getTokens()) {
                if (token.start < offset) continue;
                literal(end, token.start);
                this.tokens.push(token);
                end = token.end;
            }
            // Formula tokenization stops at a command separator. Keep the
            // unparsed suffix visible and let the checker reject it on submit.
            literal(end, limit);
            return parsed;
        };
        this.tokens = [];
        if (mode === "wff") return operand(0, "wff")!;
        const head = /^(\s*)(intro|exact|apply|rw|rwb|goal|let|qed)(?=\s|$)(\s*)/.exec(text);
        if (!head) { literal(0, text.length); return null!; }
        const [, leading, command] = head;
        literal(0, leading.length, "space");
        literal(leading.length, leading.length + command.length, "cmd");
        literal(leading.length + command.length, head[0].length, "space");
        let offset = head[0].length;
        if (command === "goal" || command === "let") {
            const separator = command === "goal" ? /^\S+?\s*:\s*/ : /^\S+?\s*:=\s*/;
            const name = separator.exec(text.slice(offset));
            if (!name) { literal(offset, text.length); return null!; }
            literal(offset, offset + name[0].length);
            offset += name[0].length;
            return operand(offset, command === "goal" ? "wff" : "cmd")!;
        }
        if (command === "rw" || command === "rwb") {
            const name = /^\S+\s*/.exec(text.slice(offset));
            if (name) {
                const patternOffset = offset + name[0].length;
                operand(offset, "cmd", patternOffset);
                return operand(patternOffset, "wff")!;
            }
        }
        if (command === "exact" || command === "apply") return operand(offset, "cmd")!;
        literal(offset, text.length);
        return null!;
    }
}

function editor(mount: HTMLElement, mode: InputMode, id: string) {
    const view = new SyntaxEditor(mount, new ProofInputParser(), "", mode);
    view.singleLine = true;
    view.input.id = id;
    view.input.rows = 1;
    view.input.enterKeyHint = "go";
    view.input.setAttribute("aria-labelledby", "hs-assistant-label");
    return view;
}

function syntax(text: string, mode: InputMode) {
    const span = document.createElement("span");
    new SyntaxViewer(span, new ProofInputParser(), text, mode);
    return span;
}

export class ProofAssistantPanel<Sheet extends object> {
    private drafts = new WeakMap<Sheet, HilbertProofAssistant>();
    private readonly label: HTMLLabelElement;
    private readonly target: SyntaxEditor;
    private readonly tactic: SyntaxEditor;
    private readonly draft: HTMLElement;
    private readonly history: HTMLElement;
    private readonly goals: HTMLElement;
    private readonly cancel: HTMLButtonElement;
    private readonly undo: HTMLButtonElement;
    private readonly status: HTMLElement;
    private readonly recommendations: HTMLElement;
    private readonly recommendationButtons: HTMLElement;
    private readonly wrapper: HTMLElement;
    private readonly targetMount: HTMLElement;
    private readonly tacticMount: HTMLElement;

    constructor(panel: HTMLElement, system: HilbertSystem, private readonly sheet: () => Sheet | undefined,
        access: () => SurvivalAccess | undefined, canEdit: () => boolean, record: (name?: string) => void) {
        const get = <T extends HTMLElement = HTMLElement>(id: string) => panel.querySelector<T>(`#hs-assistant-${id}`)!;
        const form = get<HTMLFormElement>("form");
        this.label = get<HTMLLabelElement>("label");
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
        this.wrapper = panel.querySelector(".hs-assistant-wrapper")!;

        this.target.onEnter = this.tactic.onEnter = () => form.requestSubmit();
        form.addEventListener("submit", event => {
            event.preventDefault();
            const key = sheet();
            if (!key || !canEdit()) return;
            const assistant = this.drafts.get(key);
            const text = (assistant ? this.tactic : this.target).getValue().trim();
            if (!text) return;
            this.run(() => {
                if (!assistant) {
                    this.drafts.set(key, new HilbertProofAssistant(system, text, access()));
                    this.target.setValue("");
                } else {
                    const qed = /^qed(?:\s+(.+))?$/.exec(text);
                    if (qed) {
                        const macro = assistant.qed(qed[1]);
                        this.drafts.delete(key);
                        record(macro?.name.name);
                    } else assistant.execute(text);
                    this.tactic.setValue("");
                }
                this.render(true);
            });
        });
        this.undo.addEventListener("click", () => {
            const key = sheet();
            if (!key) return;
            this.run(() => {
                if (!this.drafts.get(key)?.undo()) this.drafts.delete(key);
                this.tactic.setValue("");
                this.render(true);
            });
        });
        this.cancel.addEventListener("click", () => {
            const key = sheet();
            if (key) this.drafts.delete(key);
            this.showSheet();
            this.target.focus();
        });
        this.recommendationButtons.addEventListener("click", event => {
            if (!(event.target instanceof HTMLButtonElement)) return;
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

    private run(operation: () => void) {
        this.message("");
        try { operation(); } catch (error) {
            this.message(isHSErrorInfo(error) ? LangMgr.renderHSError(error)
                : error instanceof Error ? error.message : String(error));
            (this.tacticMount.hidden ? this.target : this.tactic).focus();
        }
        this.wrapper.scrollTop = this.wrapper.scrollHeight;
    }

    private message(text: string) {
        this.status.textContent = text;
        this.status.hidden = !text;
    }

    private render(focus = false) {
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
        if (focus) (assistant ? this.tactic : this.target).focus();
        if (!assistant) return;

        const state = assistant.snapshot();
        for (const { text } of state.history) {
            const line = document.createElement("div");
            line.append(syntax(text, "tactic"), " . ");
            this.history.append(line);
        }
        const localized = (key: "hsAssistantCurrent" | "hsAssistantReady" | "hsAssistantGoal") => {
            const span = document.createElement("span");
            span.dataset.i18n = key;
            span.textContent = LangMgr.text[key];
            return span;
        };
        if (!state.goals.length) this.goals.append(localized("hsAssistantReady"));
        for (let i = state.goals.length - 1; i >= 0; i--) {
            const { context, target } = state.goals[i];
            const line = document.createElement("div");
            line.className = i ? "hs-assistant-goal-pending" : "hs-assistant-goal-current";
            for (const { name, formula } of [...context].reverse()) {
                line.append(syntax(name, "wff"));
                if (formula !== null) line.append(" : ", syntax(formula, "wff"));
                line.append(document.createElement("br"));
            }
            line.append(document.createElement("br"));
            line.append(localized(i ? "hsAssistantGoal" : "hsAssistantCurrent"));
            if (i) line.append(`${i}：`);
            line.append(syntax(target, "wff"));
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
