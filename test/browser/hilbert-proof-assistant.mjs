import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { extname, resolve, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const module = process.env.PLAYWRIGHT_MODULE;
const { chromium } = await import(module ? pathToFileURL(module).href : 'playwright');
const root = resolve(fileURLToPath(new URL('../..', import.meta.url)));
const server = createServer(async (req, res) => {
    try {
        const path = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
        const file = resolve(root, '.' + (path === '/' ? '/index.html' : path));
        if (!file.startsWith(root + sep)) { res.writeHead(403).end(); return; }
        res.setHeader('Content-Type', ({ '.js': 'text/javascript', '.html': 'text/html', '.css': 'text/css' })[extname(file)] || 'application/octet-stream');
        res.end(await readFile(file));
    } catch { res.writeHead(404).end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
let browser;
try {
    browser = await chromium.launch({ headless: true, channel: 'chrome' });
    for (const viewport of [{ width: 1440, height: 1000 }, { width: 390, height: 844 }]) {
        const context = await browser.newContext({ viewport, locale: 'zh-CN', hasTouch: viewport.width < 400, colorScheme: viewport.width < 400 ? 'dark' : 'light' });
        try {
            const page = await context.newPage();
            const errors = [];
            page.on('pageerror', e => errors.push(e.message));
            await page.goto(`http://127.0.0.1:${server.address().port}/?creative`);
            await page.waitForFunction(() => window.game?.hsLayer?.hilbertSystem);
            await page.locator('button[data-layer="D-layer"]').click();
            const panel = page.locator('#hs-assistant');
            assert.equal(await panel.locator('label').textContent(), '证明策略：');
            const target = page.locator('#hs-assistant-target');
            const draft = page.locator('#hs-assistant-draft');
            const input = page.locator('#hs-assistant-tactic');
            const tacticPaint = page.locator('#hs-assistant-tactic-editor .editor-pre');
            const goals = page.locator('#hs-assistant-goals');
            const currentFormula = goals.locator('.hs-assistant-goal-current > span').last();
            const status = page.locator('#hs-assistant-status');
            const add = panel.getByRole('button', { name: '+', exact: true });
            const undo = panel.getByRole('button', { name: '-', exact: true });
            const cancel = panel.getByRole('button', { name: 'x', exact: true });
            const history = page.locator('#hs-assistant-history > div');
            const tactic = async text => {
                await input.fill(text);
                await input.press('Enter');
            };
            await target.evaluate(el => {
                const clipboardData = new DataTransfer();
                clipboardData.setData('text/plain', '$x>\n$x');
                el.dispatchEvent(new ClipboardEvent('paste', { clipboardData, cancelable: true }));
            });
            assert.equal(await target.inputValue(), '$x→ $x');
            await target.fill('$x; $x');
            await add.click();
            assert.equal(await status.isVisible(), true);
            assert.equal(await target.inputValue(), '$x; $x');

            await target.fill('0');
            await target.pressSequentially('@\\N');
            assert.equal(await target.inputValue(), '0∈ℕ');
            await add.click();
            const recommendations = panel.locator('#hs-assistant-recommendations');
            assert.equal(await draft.isVisible(), true);
            assert.equal(await input.isVisible(), true);
            assert.equal(await recommendations.isVisible(), false);
            assert.equal(await recommendations.locator('button').count(), 0);
            await tactic('let h := <a4(apn2) 0');
            assert.equal(await status.isVisible(), false);
            const current = goals.locator('.hs-assistant-goal-current');
            const color = locator => locator.evaluate(el => getComputedStyle(el).color);
            const goalColors = () => current.evaluate(el => [el, ...el.querySelectorAll('span')].map(node => getComputedStyle(node).color));
            const normalColors = await goalColors();
            await current.hover();
            assert.deepEqual(await goalColors(), normalColors);
            assert.match(await current.textContent(), /0∈ℕ→S\(0\)∈ℕ/);
            await cancel.click();
            assert.equal(await draft.isVisible(), false);

            const start = async formula => {
                await target.fill(formula);
                await target.press('Enter');
                assert.equal(await draft.isVisible(), true);
            };
            await start('1∈ℕ');
            await input.fill('rw d1');
            const definitions = locator => locator.locator('.token-rule-def').allTextContents();
            assert.deepEqual(await definitions(tacticPaint), ['d1']);
            await input.press('Enter');
            assert.deepEqual(await definitions(history.last()), ['d1']);
            assert.notEqual(await color(history.last().locator('.token-rule-def')), await color(history.last()));
            assert.equal(await currentFormula.textContent(), 'S(0)∈ℕ');
            await input.pressSequentially('rwb d1 (#@\\N)');
            assert.deepEqual(await definitions(tacticPaint), ['d1']);
            assert.equal(await input.inputValue(), 'rwb d1 (#∈ℕ)');
            assert.deepEqual(await tacticPaint.locator('.token-sym').allTextContents(), ['∈']);
            await input.press('Enter');
            assert.deepEqual(await definitions(history.last()), ['d1']);
            assert.equal(await currentFormula.textContent(), '1∈ℕ');
            await undo.click();
            await tactic('apply <a4(apn2) 0');
            assert.equal(await status.isVisible(), false);
            assert.equal(await currentFormula.textContent(), '0∈ℕ');
            await tactic('exact apn1');
            assert.equal(await goals.textContent(), '无目标，请输入qed结束');
            await cancel.click();

            for (const rule of ['rw d\\/', 'rw d\\/ $ ~$']) {
                await start('$∨¬$');
                await input.pressSequentially(rule);
                assert.equal(await tacticPaint.locator('.token-rule-def').textContent(), 'd\\/');
                if (rule.includes('~')) assert.equal(await input.inputValue(), 'rw d\\/ $ ¬$');
                await input.press('Enter');
                assert.equal(await status.isVisible(), false);
                assert.equal(await currentFormula.textContent(), '¬$→¬$');
                await undo.click();
                assert.equal(await currentFormula.textContent(), '$∨¬$');
                await cancel.click();
            }

            await start('∀x:x=y');
            const boundColor = await color(currentFormula.locator('.token-atom-var').last());
            const freeColor = await color(currentFormula.locator('.token-atom-free-var'));
            assert.notEqual(boundColor, freeColor);
            await tactic('intro x');
            assert.deepEqual(await currentFormula.locator('.token-atom-var').allTextContents(), ['x']);
            assert.equal(await color(currentFormula.locator('.token-atom-var')), boundColor);
            assert.equal(await color(currentFormula.locator('.token-atom-free-var')), freeColor);
            assert.deepEqual(await current.locator(':scope > .token-atom-var').allTextContents(), ['x']);
            assert.equal(await color(history.last().locator('.token-atom-var')), boundColor);
            await undo.click();
            assert.equal(await currentFormula.textContent(), '∀x:x=y');
            assert.equal(await current.locator(':scope > .token-atom-var').count(), 0);
            await cancel.click();

            await start('∀x:(x=y→x=y)');
            await tactic('intro $z');
            await tactic('intro h');
            assert.deepEqual(await current.locator('.token-atom-var').allTextContents(), ['$z', '$z', '$z']);
            assert.deepEqual(await current.locator('.token-atom-free-var').allTextContents(), ['h', 'y', 'y']);
            assert.deepEqual(await history.first().locator('.token-atom-var').allTextContents(), ['$z']);
            assert.equal(await history.last().locator('.token-atom-var').count(), 0);
            await cancel.click();

            await start('a=b→b=a→a=a');
            await tactic('intro h');
            await tactic('intro p');
            await tactic('rw h #=z');
            assert.equal(await status.isVisible(), true);
            assert.equal(await currentFormula.textContent(), 'a=a');
            await tactic('rw h');
            assert.equal(await currentFormula.textContent(), 'b=b');
            await undo.click();
            assert.equal(await currentFormula.textContent(), 'a=a');
            await tactic('rw h (#=a)');
            assert.equal(await status.isVisible(), false);
            assert.equal(await currentFormula.textContent(), 'b=a');
            assert.equal(await recommendations.getByRole('button', { name: 'exact p', exact: true }).isVisible(), true);
            await tactic('exact p');
            assert.equal(await goals.textContent(), '无目标，请输入qed结束');
            await cancel.click();

            await start('(P↔Q)→(P→Q)→(Q→Q)');
            await tactic('intro h');
            await tactic('intro p');
            await input.pressSequentially('rwb h (#>Q)');
            assert.equal(await input.inputValue(), 'rwb h (#→Q)');
            assert.deepEqual(await tacticPaint.locator('.token-sym').allTextContents(), ['→']);
            await input.press('Enter');
            assert.equal(await status.isVisible(), false);
            assert.equal(await currentFormula.textContent(), 'P→Q');
            await tactic('exact p');
            assert.equal(await goals.textContent(), '无目标，请输入qed结束');
            await cancel.click();

            const statement = '($x→$y)→$x→$y';
            await target.pressSequentially('($x>$y)>$x>$y');
            assert.equal(await target.inputValue(), statement);
            const targetPaint = page.locator('#hs-assistant-target-editor .editor-pre');
            assert.equal(await targetPaint.textContent(), statement);
            assert.deepEqual(await targetPaint.locator('.token-sym').allTextContents(), ['→', '→', '→']);
            await target.press('Enter');
            assert.equal(await draft.isVisible(), true);
            assert.equal(await panel.locator('#hs-assistant-statement').count(), 0);
            assert.equal(await currentFormula.textContent(), statement);
            assert.match(await goals.textContent(), /^当前目标：/);
            const initial = panel.getByRole('button', { name: 'intro h', exact: true });
            await initial.click();
            assert.deepEqual(await history.allTextContents(), ['intro h . ']);
            await undo.click();
            assert.deepEqual(await history.allTextContents(), []);
            assert.equal(await currentFormula.textContent(), statement);
            await tactic('intro f');

            await input.pressSequentially('goal aux : $z>$z');
            assert.equal(await input.inputValue(), 'goal aux : $z→$z');
            assert.equal(await page.locator('#hs-assistant-tactic-editor .token-cmd').textContent(), 'goal');
            await add.click();
            assert.equal(await goals.locator('.hs-assistant-goal-pending').count(), 1);
            assert.equal(await currentFormula.textContent(), '$z→$z');
            await tactic('intro h');
            await tactic('exact h');
            await tactic('let g := f');
            await tactic('intro p');
            await tactic('apply g');
            assert.equal(await currentFormula.textContent(), '$x');
            await undo.click();
            assert.equal(await currentFormula.textContent(), '$y');
            await panel.getByRole('button', { name: 'apply g', exact: true }).click();
            assert.equal(await currentFormula.textContent(), '$x');
            await tactic('exact aux');
            assert.equal(await status.isVisible(), true);
            assert.equal(await input.inputValue(), 'exact aux');
            assert.equal(await currentFormula.textContent(), '$x');
            assert.equal(await page.evaluate(() => window.game.hsLayer.hilbertSystem.props.length), 0);

            await page.locator('.sheet-tab-add').click();
            assert.equal(await target.isVisible(), true);
            assert.equal(await draft.isVisible(), false);
            await page.locator('.sheet-tab').first().click();
            assert.equal(await currentFormula.textContent(), '$x');
            await panel.getByRole('button', { name: 'exact p', exact: true }).click();
            assert.equal(await goals.textContent(), '无目标，请输入qed结束');
            assert.equal(await panel.getByRole('button', { name: 'qed', exact: true }).isVisible(), true);
            await tactic('qed sAssistant');
            assert.equal(await target.isVisible(), true);
            assert.equal(await status.isVisible(), false);

            await page.evaluate(async statement => {
                const { HSParser } = await import('/js/hs/core/parser.js');
                const layer = window.game.hsLayer;
                const hs = layer.hilbertSystem;
                const saved = structuredClone(layer.serialize());
                layer.deserialize(saved);
                const root = new HSParser().parse(statement, 'wff');
                if (!hs.checkConclusionInPropList().conclusion.equal(root)) throw new Error('Sheet conclusion changed after loading.');
                if (!hs.rules.get('sAssistant')?.step?.length) throw new Error('Macro did not survive loading.');
            }, statement);
            await page.locator('.sheet-tab-add').click();
            await start('$∨¬$');
            await tactic('rw d\\/');
            assert.equal(await currentFormula.textContent(), '¬$→¬$');
            await tactic('exact .i');
            await tactic('qed');
            assert.equal(await target.isVisible(), true);
            assert.equal(await status.isVisible(), false);
            const recorded = await page.evaluate(() => window.game.hsLayer.hilbertSystem.genCmd());
            assert.deepEqual(recorded, ['.i ¬$', 'msbt<(d\\/) 1 0']);

            assert.deepEqual(errors, []);
            console.log(`Proof assistant passed at ${viewport.width}×${viewport.height}`);
        } finally { await context.close(); }
    }
} finally {
    await browser?.close();
    server.close();
}
