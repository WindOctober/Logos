#!/usr/bin/env python3
"""Host-owned lemma availability and navigation surfaces (not SQL semantics).

The full checked authority is unchanged. Enabled lemmas are trusted leaves;
bag-dependent wrappers join the bag group. Disabled names cannot be referenced
by candidates or by their printed elaborated proof terms. Agent navigation is
source-only, without hidden proofs, objects, catalog cards or build artifacts.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys

spec = importlib.util.spec_from_file_location(
    "declaration_search", Path(__file__).with_name("search-rocq-declarations.py")
)
search = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = search
spec.loader.exec_module(search)

VERSION = 1
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
DECL = re.compile(
    r"(?<![A-Za-z0-9_'])(?:(?:Local|Global|Polymorphic|Monomorphic|Program)\s+)*(?P<kind>Lemma|Theorem|Corollary|Fact|Proposition|Remark|Example|Definition|Let|Fixpoint|CoFixpoint|Instance|Ltac)\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])"
)
PROOF = re.compile(r"\bProof\b[^.]*\.")
END = re.compile(r"\b(?:Qed|Defined|Admitted|Abort)\s*\.")
MARKER = "LOGOS_PRIVATE_ABLATION_PROOF_TERMS"
BAG = re.compile(r"bag|Bag|Febag|query_.*permutation|query_.*permut|tnull_.*permut")
ABSTRACTION = re.compile(r"(?:^|[^A-Za-z0-9]|_)(?:alpha|gamma)(?:$|[^A-Za-z0-9]|_)")
FINITE_BAG_MODULE = re.compile(r"(?:^|\.)(?:FiniteBag|FiniteBagImpl)(?:\.|$)")


def declarations(text):
    masked = search.mask_comments_and_strings(text)
    matches = list(DECL.finditer(masked))
    for i, match in enumerate(matches):
        limit = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        end = search.sentence_end(masked, match.end()) + 1
        proof = PROOF.search(masked, end, limit)
        terminator = END.search(masked, end, limit)
        finish = terminator.end() if terminator else end
        yield dict(
            name=match["name"],
            kind=match["kind"],
            start=match.start(),
            end=end,
            finish=finish,
            proof=proof.start() if proof else None,
            statement=text[match.start() : end],
            text=text[match.start() : finish],
            tokens=set(IDENT.findall(masked[match.end() : finish])),
        )


def inventory(root):
    root, sources = search.authority_sources(root)
    records = search.parse_sources(root, sources)
    texts = {}
    known = {r.fqn for r in records}
    for source in sources:
        text = source.content.decode()
        events = search.scope_events(search.mask_comments_and_strings(text))
        scopes, event_index = [], 0
        for declaration in declarations(text):
            while (
                event_index < len(events)
                and events[event_index].position < declaration["start"]
            ):
                event = events[event_index]
                if event.action == "open":
                    scopes.append((event.kind, event.name))
                elif scopes and scopes[-1][1] == event.name:
                    scopes.pop()
                event_index += 1
            relative = source.path.relative_to(root).as_posix()
            module = ".".join(
                (
                    *source.root.logical_prefix,
                    *source.path.relative_to(source.root.path).with_suffix("").parts,
                    *(name for kind, name in scopes if kind == "module"),
                )
            )
            fqn = module + "." + declaration["name"]
            texts[fqn] = declaration
            # Availability includes local/transparent facts too, not only the
            # public Qed declarations normally advertised by search.
            if fqn not in known and declaration["kind"] in {
                "Lemma",
                "Theorem",
                "Corollary",
                "Fact",
                "Proposition",
                "Remark",
                "Example",
            }:
                records.append(
                    search.Declaration(
                        fqn,
                        declaration["name"],
                        declaration["kind"],
                        module,
                        relative,
                        text.count("\n", 0, declaration["start"]) + 1,
                        declaration["statement"],
                        None,
                        tuple(
                            sorted(
                                set(
                                    IDENT.findall(
                                        search.mask_comments_and_strings(
                                            declaration["statement"]
                                        )
                                    )
                                )
                            )
                        ),
                    )
                )
                known.add(fqn)
    records.sort(key=lambda r: (r.fqn, r.source, r.line))
    by_name = {}
    for record in records:
        by_name.setdefault(record.name, []).append(record.fqn)
    groups = {}
    dependencies = {}
    for record in records:
        declaration = texts.get(record.fqn)
        if declaration is None:
            raise ValueError(f"cannot bind declaration {record.fqn}")
        # Group on public semantic vocabulary, not just theorem names. Pure
        # Boolean-operand permutations are not result-bag lifting.
        signature = (
            record.name + " " + search.mask_comments_and_strings(record.statement)
        )
        groups[record.fqn] = (
            "bag"
            if (
                BAG.search(signature)
                or ABSTRACTION.search(signature)
                or FINITE_BAG_MODULE.search(record.module)
                or "=BE=" in signature
            )
            else "other"
        )
        dependencies[record.fqn] = {
            fqn
            for token in declaration["tokens"]
            for fqn in by_name.get(token, [])
            if fqn != record.fqn
        }
    # Prevent the other switch from exporting a wrapper around disabled bag
    # facts. Ambiguous short names conservatively include every matching edge.
    changed = True
    while changed:
        changed = False
        for name, deps in dependencies.items():
            same_name = by_name[name.rsplit(".", 1)[-1]]
            if groups[name] == "other" and any(
                groups[d] == "bag" for d in deps | set(same_name)
            ):
                groups[name] = "bag"
                changed = True
    return root, sources, records, groups


def hidden_tokens(text, policy):
    return sorted(
        set(IDENT.findall(search.mask_comments_and_strings(text)))
        & set(policy["disabledNames"])
    )


def navigation_source(text, disabled):
    # No proof bodies or tactic programs are advertised in an ablated view,
    # including the bodies of enabled lemmas (which may use hidden helpers).
    masked = search.mask_comments_and_strings(text, preserve_strings=True)
    edits = []
    for d in declarations(text):
        if d["name"] in disabled or d["kind"] == "Ltac":
            edits.append(
                (
                    d["start"],
                    d["finish"],
                    "\n" * text[d["start"] : d["finish"]].count("\n"),
                )
            )
        elif d["proof"] is not None:
            edits.append(
                (
                    d["end"],
                    d["finish"],
                    "(* Checked proof omitted from this navigation view. *)"
                    + "\n" * text[d["end"] : d["finish"]].count("\n"),
                )
            )
    for start, end, replacement in reversed(edits):
        masked = masked[:start] + replacement + masked[end:]
    # Remaining comments and registration commands can disclose disabled names.
    lines = []
    for line in masked.splitlines():
        if set(IDENT.findall(line)) & disabled:
            lines.append("(* Hidden proof-support reference. *)")
        else:
            lines.append(line.rstrip())
    return (
        "(* Navigation-only source view; not an input to the compiler. *)\n"
        + "\n".join(lines)
        + "\n"
    )


def prepare(root, output, bag, other, baseline):
    root, sources, records, groups = inventory(root)
    disabled = {
        r.name for r in records if not (bag if groups[r.fqn] == "bag" else other)
    }
    policy = dict(
        schemaVersion=VERSION,
        groupingPolicy="bag-vocabulary-abstraction-finite-bag-and-transitive-wrappers-v1",
        bagLemmas=bag,
        otherLemmas=other,
        authoritySha256=search.index_key(root, sources),
        helperSha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        searchHelperSha256=hashlib.sha256(
            Path(search.__file__).read_bytes()
        ).hexdigest(),
        disabledNames=sorted(disabled),
        declarations=[dict(fqn=r.fqn, group=groups[r.fqn]) for r in records],
        baseline={
            d["name"]: hashlib.sha256(d["text"].encode()).hexdigest()
            for d in declarations(baseline.read_text())
        },
    )
    output.mkdir(parents=True, exist_ok=True)
    previous = output / "lemma-policy.json"
    if previous.exists():
        old = json.loads(previous.read_text())
        if any(
            old.get(key) != policy[key]
            for key in (
                "bagLemmas",
                "otherLemmas",
                "authoritySha256",
                "helperSha256",
                "searchHelperSha256",
            )
        ):
            raise ValueError(
                "lemma availability/authority cannot change within a run; use a fresh log directory"
            )
    (output / "lemma-policy.json").write_text(json.dumps(policy, indent=2) + "\n")
    view = output / "lemma-surface"
    view.mkdir(exist_ok=True)
    allowed = [
        dataclasses.replace(
            r,
            line=r.line + 1,  # one navigation-only header; all other lines preserved
            statement=search.mask_comments_and_strings(
                r.statement, preserve_strings=True
            ),
        )
        for r in records
        if r.name not in disabled
    ]
    # Use the exact records consumed by the normal search filter/page code.
    index = dict(
        schemaVersion=VERSION,
        bagLemmas=bag,
        otherLemmas=other,
        declarations=[dataclasses.asdict(r) for r in allowed],
    )
    (view / "lemma-surface.json").write_text(json.dumps(index, indent=2) + "\n")
    for source in sources:
        dest = view / source.path.relative_to(root)
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(navigation_source(source.content.decode(), disabled))
    summary = {k: policy[k] for k in ("schemaVersion", "bagLemmas", "otherLemmas")}
    summary.update(
        availableDeclarations=len(allowed),
        disabledDeclarations=len(records) - len(allowed),
        bagDeclarations=sum(g == "bag" for g in groups.values()),
        otherDeclarations=sum(g == "other" for g in groups.values()),
        policySha256=hashlib.sha256(
            (output / "lemma-policy.json").read_bytes()
        ).hexdigest(),
        boundary="preproved-lemma-availability; definitions, constructors, Rocq standard library and exact generated scaffolding remain fixed",
    )
    (output / "lemma-availability.json").write_text(
        json.dumps(summary, indent=2) + "\n"
    )


def context_tree(source, target, policy):
    target.mkdir(parents=True, exist_ok=True)
    names = (
        "Schema.v Queries.v WitnessData.v Witness.v Goal.v source.sql target.sql "
        "query-shape.json ordered-signatures.json observation-certificates.json "
        "semantic-primer.md search-rocq-declarations.py context-manifest.json "
        "lemma-availability.json proof-agent-prompt.md run-rocq-check.sh"
    ).split()
    for name in names:
        src = source / name
        if not src.is_file():
            raise ValueError(f"missing context file: {name}")
        if src.suffix == ".v":
            (target / name).write_text(
                navigation_source(src.read_text(), set(policy["disabledNames"]))
            )
        else:
            shutil.copyfile(src, target / name)
    for name in ["WitnessModules", "ProofModules"]:
        (target / name).mkdir(exist_ok=True)
        for src in (source / name).glob("*.v"):
            dest = target / name / src.name
            # User-authored published proofs are part of the experiment, not
            # a hidden library. Preserve them exactly for later composition.
            dest.write_text(
                src.read_text()
                if name == "ProofModules"
                else navigation_source(src.read_text(), set(policy["disabledNames"]))
            )
    order = source / "WitnessModules/ORDER"
    if order.is_file():
        shutil.copyfile(order, target / "WitnessModules/ORDER")


def source_check(text, policy):
    # Imports of the fixed authority are permitted; prohibited constants are
    # not. Names are checked before execution, including qualified references.
    for d in reversed(list(declarations(text))):
        if (
            policy["baseline"].get(d["name"])
            == hashlib.sha256(d["text"].encode()).hexdigest()
        ):
            text = (
                text[: d["start"]]
                + " " * (d["finish"] - d["start"])
                + text[d["finish"] :]
            )
    hidden = hidden_tokens(text, policy)
    if hidden:
        raise ValueError("disabled lemma reference: " + ", ".join(hidden[:8]))
    tokens = set(IDENT.findall(search.mask_comments_and_strings(text)))
    if tokens & {
        "Print",
        "About",
        "Search",
        "SearchPattern",
        "SearchRewrite",
        "Locate",
        "Hint",
        "Hints",
        "Goal",
        "Save",
        "Program",
        "Obligation",
        "Obligations",
        "Derive",
        "Scheme",
    }:
        raise ValueError(
            "ablation: use the filtered index and explicit named declarations; introspection, hint registration and implicit declarations are disabled"
        )


def instrument(source, target, policy):
    text = source.read_text()
    source_check(text, policy)
    edits = []
    for d in declarations(text):
        if (
            policy["baseline"].get(d["name"])
            == hashlib.sha256(d["text"].encode()).hexdigest()
        ):
            continue
        if re.search(r"\bLtac\b", d["statement"]):
            continue
        # Print while the declaration's Module/Section is still open. These
        # private frames are removed before any output is returned to an agent.
        suffix = (
            f'\nGoal True. idtac "{MARKER}". Abort.\n'
            'Set Printing All.\nSet Printing Depth 1000000.\nSet Printing Width 1000000.\n'
            f"Print {d['name']}.\nUnset Printing All.\n"
            f'Goal True. idtac "{MARKER}_END". Abort.\n'
        )
        edits.append((d["finish"], suffix))
    for position, suffix in reversed(edits):
        text = text[:position] + suffix + text[position:]
    # Always emit a completion marker, including an empty or baseline module.
    target.write_text(text + f'\nGoal True. idtac "{MARKER}_COMPLETE". Abort.\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    p = sub.add_parser("prepare")
    p.add_argument("--authority", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--baseline", type=Path, required=True)
    p.add_argument("--bag", choices=["on", "off"], required=True)
    p.add_argument("--other", choices=["on", "off"], required=True)
    for action in [
        "source-check",
        "instrument",
        "check-output",
        "context-tree",
    ]:
        p = sub.add_parser(action)
        p.add_argument("--policy", type=Path, required=True)
        p.add_argument("--source", type=Path, required=True)
        if action in ["instrument", "context-tree"]:
            p.add_argument("--target", type=Path, required=True)
        if action == "check-output":
            p.add_argument("--compile-status", type=int, default=0)
    args = parser.parse_args()
    if args.action == "prepare":
        prepare(
            args.authority,
            args.output,
            args.bag == "on",
            args.other == "on",
            args.baseline,
        )
        return
    policy = json.loads(args.policy.read_text())
    if args.action == "source-check":
        source_check(
            sys.stdin.read() if str(args.source) == "-" else args.source.read_text(),
            policy,
        )
    elif args.action == "instrument":
        instrument(args.source, args.target, policy)
    elif args.action == "context-tree":
        context_tree(args.source, args.target, policy)
    else:
        text = args.source.read_text()
        public = re.sub(
            re.escape(MARKER) + r"\n.*?(?:" + re.escape(MARKER) + r"_END\n?|\Z)",
            "",
            text,
            flags=re.S,
        )
        public = public.replace(MARKER + "_COMPLETE", "")
        print(public, end="")
        if args.compile_status:
            sys.exit(args.compile_status)
        frames = re.findall(
            re.escape(MARKER) + r"\n(.*?)" + re.escape(MARKER) + r"_END", text, re.S
        )
        private = "\n".join(frames)
        hidden = hidden_tokens(private, policy)
        if hidden:
            raise ValueError(
                "elaborated proof uses a disabled library lemma; prove this step explicitly from available declarations"
            )
        if re.search(r"\.\.\.|…", search.mask_comments_and_strings(private)):
            raise ValueError("ablation proof-term output was truncated")
        if MARKER + "_COMPLETE" not in text:
            raise ValueError("ablation proof-term inspection did not complete")
        print("LOGOS_LEMMA_ABLATION proof_terms=accepted", file=sys.stderr)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, search.SearchError) as error:
        print(f"lemma ablation: {error}", file=sys.stderr)
        sys.exit(1)
