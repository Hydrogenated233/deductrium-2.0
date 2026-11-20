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
        const context = await browser.newContext({ viewport, hasTouch: viewport.width < 400 });
        try {
            const page = await context.newPage();
            const errors = [];
            page.on('pageerror', e => errors.push(e.message));
            await page.goto(`http://127.0.0.1:${server.address().port}/?creative`);
            await page.waitForFunction(() => window.game?.hsLayer?.hilbertSystem);
            await page.locator('button[data-layer="D-layer"]').click();
            await page.locator('#hs-assistant summary').click();
            const target = page.locator('#hs-assistant-target');
            const draft = page.locator('#hs-assistant-draft');
            const input = page.locator('#hs-assistant-tactic');
            const goals = page.locator('#hs-assistant-goals > li > code');
            const status = page.locator('#hs-assistant-status');
            const tactic = async text => {
                await input.fill(text);
                await input.press('Enter');
            };
            const statement = '($x→$y)→$x→$y';
            await target.fill(statement);
            await target.press('Enter');
            await tactic('intro f');
            await tactic('goal aux : $z→$z');
            await tactic('intro h');
            await tactic('exact h');
            await tactic('let g := f');
            await tactic('intro p');
            await tactic('apply g');
            assert.deepEqual(await goals.allTextContents(), ['⊢ $x']);
            await tactic('exact aux');
            assert.equal(await status.isVisible(), true);
            assert.equal(await input.inputValue(), 'exact aux');
            assert.deepEqual(await goals.allTextContents(), ['⊢ $x']);
            assert.equal(await page.evaluate(() => window.game.hsLayer.hilbertSystem.props.length), 0);

            await page.locator('.sheet-tab-add').click();
            assert.equal(await target.isVisible(), true);
            assert.equal(await draft.isVisible(), false);
            await page.locator('.sheet-tab').first().click();
            assert.deepEqual(await goals.allTextContents(), ['⊢ $x']);
            await tactic('exact p');
            assert.equal(await page.locator('#hs-assistant-ready').isVisible(), true);
            await tactic('qed sAssistant');
            assert.equal(await target.isVisible(), true);
            assert.equal(await status.isVisible(), true);

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
            assert.deepEqual(errors, []);
            console.log(`Proof assistant passed at ${viewport.width}×${viewport.height}`);
        } finally { await context.close(); }
    }
} finally {
    await browser?.close();
    server.close();
}
