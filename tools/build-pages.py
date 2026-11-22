"""Build a Pages site from the fetched origin branches without running their code."""

import argparse
from html import escape
from io import BytesIO
from pathlib import Path
import subprocess
import tarfile
from urllib.parse import quote


REMOTE_PREFIX = "refs/remotes/origin/"
RUNTIME_PATHS = ("index.html", "draw.html", "js", "lib", "style", "examples")


def git(*args):
    return subprocess.check_output(("git", *args))


def build(output):
    refs = git("for-each-ref", "--format=%(refname)%09%(objectname)%09%(symref)", REMOTE_PREFIX)
    branches = []
    for line in refs.decode("utf-8").split("\n"):
        if not line:
            continue
        ref, commit, symref = line.split("\t")
        if not symref:
            branches.append((ref.removeprefix(REMOTE_PREFIX), commit))

    output.mkdir()
    links = []
    for name, commit in sorted(branches, key=lambda branch: (branch[0] != "main", branch[0])):
        root_entries = set(git("ls-tree", "--name-only", "-z", commit).split(b"\0"))
        if b"index.html" not in root_entries:
            print(f"Skipping {name}: no index.html")
            continue
        paths = [path for path in RUNTIME_PATHS if path.encode() in root_entries]
        archive = git("archive", "--format=tar", commit, "--", *paths)
        target = output / "branches" / name
        with tarfile.open(fileobj=BytesIO(archive)) as tar:
            members = tar.getmembers()
            if not all(member.isdir() or member.isreg() for member in members):
                raise ValueError(f"{name}: only regular runtime files are supported")
            tar.extractall(target, filter="data")
        if not (target / "index.html").is_file():
            raise ValueError(f"{name}: archive has no playable index.html")
        links.append(f'    <li><a href="branches/{quote(name)}/">{escape(name)}</a></li>')
        print(f"Published {name} ({commit[:12]})")

    if not links:
        raise ValueError("No playable branches found. Fetch the origin branches first.")

    index = "\n".join([
        "<!doctype html>",
        '<html lang="zh-CN">',
        "<head>",
        '  <meta charset="utf-8">',
        '  <meta name="viewport" content="width=device-width, initial-scale=1">',
        "  <title>Deductrium 2.0 · 选择分支</title>",
        "</head>",
        "<body>",
        "  <h1>Deductrium 2.0</h1>",
        "  <p>选择分支：</p>",
        "  <ul>",
        *links,
        "  </ul>",
        "</body>",
        "</html>",
        "",
    ])
    (output / "index.html").write_text(index, encoding="utf-8")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="New directory for the Pages artifact")
    build(parser.parse_args().output)
