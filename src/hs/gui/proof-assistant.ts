import { LangMgr } from "../../lang.js";
import type { SurvivalAccess } from "../access.js";
import type { HilbertSystem } from "../core/core.js";
import { isHSErrorInfo } from "../core/error.js";
import { HilbertProofAssistant } from "../proof-assistant.js";

export class ProofAssistantPanel<Sheet extends object> {
    private drafts = new WeakMap<Sheet, HilbertProofAssistant>();
    private readonly start: HTMLFormElement;
    private readonly target: HTMLInputElement;
    private readonly tactic: HTMLInputElement;
    private readonly draft: HTMLElement;
    private readonly statement: HTMLElement;
    private readonly goals: HTMLElement;
    private readonly ready: HTMLElement;
    private readonly status: HTMLElement;

    constructor(panel: HTMLElement, system: HilbertSystem, private readonly sheet: () => Sheet | undefined,
        access: () => SurvivalAccess | undefined, canEdit: () => boolean, record: (name?: string) => void) {
        this.start = panel.querySelector<HTMLFormElement>("#hs-assistant-start")!;
        this.target = panel.querySelector<HTMLInputElement>("#hs-assistant-target")!;
        this.tactic = panel.querySelector<HTMLInputElement>("#hs-assistant-tactic")!;
        this.draft = panel.querySelector<HTMLElement>("#hs-assistant-draft")!;
        this.statement = panel.querySelector<HTMLElement>("#hs-assistant-statement")!;
        this.goals = panel.querySelector<HTMLElement>("#hs-assistant-goals")!;
        this.ready = panel.querySelector<HTMLElement>("#hs-assistant-ready")!;
        this.status = panel.querySelector<HTMLElement>("#hs-assistant-status")!;
        this.start.addEventListener("submit", event => {
            event.preventDefault();
            const key = sheet();
            if (!key || !canEdit()) return;
            this.run(() => {
                this.drafts.set(key, new HilbertProofAssistant(system, this.target.value, access()));
                this.render();
                this.tactic.focus();
            });
        });
        panel.querySelector("#hs-assistant-command")!.addEventListener("submit", event => {
            event.preventDefault();
            const key = sheet();
            if (!key || !canEdit()) return;
            const assistant = this.drafts.get(key);
            if (!assistant) return;
            const text = this.tactic.value.trim();
            this.run(() => {
                const qed = /^qed(?:\s+(.+))?$/.exec(text);
                if (qed) {
                    const macro = assistant.qed(qed[1]);
                    this.drafts.delete(key);
                    this.target.value = "";
                    record(macro?.name.name);
                    this.render();
                    this.message(LangMgr.text.hsAssistantRecorded);
                    this.target.focus();
                } else {
                    assistant.execute(text);
                    this.render();
                    this.tactic.focus();
                }
                this.tactic.value = "";
            });
        });
        panel.querySelector("#hs-assistant-cancel")!.addEventListener("click", () => {
            const key = sheet();
            if (key) this.drafts.delete(key);
            this.showSheet();
            this.target.focus();
        });
        this.render();
    }

    reset() {
        this.drafts = new WeakMap();
        this.showSheet();
    }

    showSheet() {
        this.target.value = this.tactic.value = "";
        this.message("");
        this.render();
    }

    private run(operation: () => void) {
        this.message("");
        try { operation(); } catch (error) {
            this.message(isHSErrorInfo(error) ? LangMgr.renderHSError(error)
                : error instanceof Error ? error.message : String(error), true);
        }
    }

    private message(text: string, error = false) {
        this.status.textContent = text;
        this.status.hidden = !text;
        this.status.classList.toggle("hs-assistant-error", error);
    }

    private render() {
        const key = this.sheet();
        const state = key && this.drafts.get(key)?.snapshot();
        this.start.hidden = !!state;
        this.draft.hidden = !state;
        if (!state) return;
        this.statement.textContent = `⊢ ${state.target}`;
        this.ready.hidden = !!state.goals.length;
        this.goals.replaceChildren(...state.goals.map(({ target, context }, index) => {
            const li = document.createElement("li");
            if (!index) {
                li.setAttribute("aria-current", "step");
                if (context.length) {
                    const bindings = document.createElement("ul");
                    for (const { name, formula } of context) {
                        const binding = document.createElement("li");
                        binding.textContent = formula === null ? name : `${name} : ${formula}`;
                        bindings.append(binding);
                    }
                    li.append(bindings);
                }
            }
            const formula = document.createElement("code");
            formula.textContent = `⊢ ${target}`;
            li.append(formula);
            return li;
        }));
    }
}
