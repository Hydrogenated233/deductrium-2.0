import { LangMgr } from "../../lang.js";
import { isHSErrorInfo } from "../core/error.js";
import { HilbertProofAssistant } from "../proof-assistant.js";
export class ProofAssistantPanel {
    sheet;
    drafts = new WeakMap();
    start;
    target;
    tactic;
    draft;
    statement;
    goals;
    ready;
    status;
    constructor(panel, system, sheet, access, canEdit, record) {
        this.sheet = sheet;
        this.start = panel.querySelector("#hs-assistant-start");
        this.target = panel.querySelector("#hs-assistant-target");
        this.tactic = panel.querySelector("#hs-assistant-tactic");
        this.draft = panel.querySelector("#hs-assistant-draft");
        this.statement = panel.querySelector("#hs-assistant-statement");
        this.goals = panel.querySelector("#hs-assistant-goals");
        this.ready = panel.querySelector("#hs-assistant-ready");
        this.status = panel.querySelector("#hs-assistant-status");
        this.start.addEventListener("submit", event => {
            event.preventDefault();
            const key = sheet();
            if (!key || !canEdit())
                return;
            this.run(() => {
                this.drafts.set(key, new HilbertProofAssistant(system, this.target.value, access()));
                this.render();
                this.tactic.focus();
            });
        });
        panel.querySelector("#hs-assistant-command").addEventListener("submit", event => {
            event.preventDefault();
            const key = sheet();
            if (!key || !canEdit())
                return;
            const assistant = this.drafts.get(key);
            if (!assistant)
                return;
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
                }
                else {
                    assistant.execute(text);
                    this.render();
                    this.tactic.focus();
                }
                this.tactic.value = "";
            });
        });
        panel.querySelector("#hs-assistant-cancel").addEventListener("click", () => {
            const key = sheet();
            if (key)
                this.drafts.delete(key);
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
    run(operation) {
        this.message("");
        try {
            operation();
        }
        catch (error) {
            this.message(isHSErrorInfo(error) ? LangMgr.renderHSError(error)
                : error instanceof Error ? error.message : String(error), true);
        }
    }
    message(text, error = false) {
        this.status.textContent = text;
        this.status.hidden = !text;
        this.status.classList.toggle("hs-assistant-error", error);
    }
    render() {
        const key = this.sheet();
        const state = key && this.drafts.get(key)?.snapshot();
        this.start.hidden = !!state;
        this.draft.hidden = !state;
        if (!state)
            return;
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
//# sourceMappingURL=proof-assistant.js.map