"""
Post-process traced theorem data (train/val/test.json) into a dependency analysis.

For each theorem, extract premise references from ``annotated_tactic`` and split
them into:
  - internal deps: premises that are themselves theorems in the input files
  - external premises: everything else (names only)

Outputs:
  - a text report: per-theorem blocks + a topologically ordered DAG listing
  - optional graph rendering (networkx + matplotlib, layered DAG layout)

Usage:
  python tracelocal_postprocess.py INPUT.json [INPUT2.json ...] \
      [--out report.txt] [--graph graph.png] [--no-premise-nodes]

Multiple inputs are merged (e.g. train/val/test -> full repo view).
"""

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

# --------------- data loading ---------------


def load_theorems(paths: list[str]) -> list[dict]:
    """Load theorems from one or more split JSON files, dedup by identity."""
    seen: dict[tuple, dict] = {}
    for p in paths:
        data = json.loads(Path(p).read_text())
        for t in data:
            key = (t["file_path"], t["full_name"], tuple(t["start"]))
            seen.setdefault(key, t)
    # stable order: by file, then by source position
    return sorted(seen.values(), key=lambda t: (t["file_path"], t["start"]))


def extract_premises(theorem: dict) -> dict[str, list[str]]:
    """Return {premise_full_name: [tactics that used it]} for one theorem."""
    used: dict[str, list[str]] = defaultdict(list)
    for tac in theorem.get("traced_tactics", []):
        ann = tac.get("annotated_tactic", [])
        if len(ann) == 2 and isinstance(ann[1], list):
            for p in ann[1]:
                if isinstance(p, dict) and p.get("full_name"):
                    used[p["full_name"]].append(tac["tactic"])
    return used


# --------------- dependency analysis ---------------


def classify_deps(theorems: list[dict]) -> dict[str, dict]:
    """For each theorem, split premises into internal (other theorems) and external."""
    exact = {t["full_name"] for t in theorems}
    # suffix index for namespaced references (e.g. 'Foo.bar' vs theorem 'bar')
    suffix: dict[str, list[str]] = defaultdict(list)
    for n in exact:
        suffix[n.split(".")[-1]].append(n)

    result: dict[str, dict] = {}
    for t in theorems:
        internal: dict[str, list[str]] = defaultdict(list)
        external: dict[str, list[str]] = defaultdict(list)
        for name, tactics in extract_premises(t).items():
            if name in exact:
                internal[name] = tactics
            elif len(suffix.get(name.split(".")[-1], [])) == 1:
                internal[suffix[name.split(".")[-1]][0]] = tactics
            else:
                external[name] = tactics
        result[t["full_name"]] = {"internal": internal, "external": external}
    return result


def topo_levels(theorems: list[dict], deps: dict[str, dict]) -> tuple[list[str], dict[str, int], bool]:
    """Kahn's algorithm; level(n) = longest path from a root. Returns order, levels, had_cycle."""
    names = [t["full_name"] for t in theorems]
    name_set = set(names)
    edges = {n: {d for d in deps[n]["internal"] if d in name_set and d != n} for n in names}
    indeg = {n: 0 for n in names}
    for src, dsts in edges.items():
        for d in dsts:
            indeg[d] += 1
    level = {n: 0 for n in names}
    queue = sorted([n for n in names if indeg[n] == 0])
    order: list[str] = []
    while queue:
        n = queue.pop(0)
        order.append(n)
        for d in sorted(edges[n]):
            level[d] = max(level[d], level[n] + 1)
            indeg[d] -= 1
            if indeg[d] == 0:
                queue.append(d)
    had_cycle = len(order) < len(names)
    if had_cycle:  # append remaining nodes defensively (shouldn't happen for Lean)
        order += [n for n in names if n not in order]
    return order, level, had_cycle


# --------------- report ---------------


def build_report(theorems: list[dict], deps: dict[str, dict], order: list[str],
                 level: dict[str, int], had_cycle: bool, inputs: list[str]) -> str:
    L: list[str] = []
    L.append("=" * 70)
    L.append("定理-Premise 依赖分析报告")
    L.append("=" * 70)
    L.append(f"输入: {', '.join(inputs)}")
    n_internal = sum(len(d["internal"]) for d in deps.values())
    all_ext = {n for d in deps.values() for n in d["external"]}
    L.append(f"定理总数: {len(theorems)} | 定理间依赖边: {n_internal} "
             f"| 去重后外部premise: {len(all_ext)}")
    if had_cycle:
        L.append("警告: 检测到依赖环(Lean中不应出现), 已强制排序")

    by_name = {t["full_name"]: t for t in theorems}
    by_level: dict[int, list[str]] = defaultdict(list)
    for n in order:
        by_level[level[n]].append(n)

    L.append("")
    L.append("-" * 70)
    L.append("一、DAG 视角(拓扑分层; L=k 表示依赖链最长深度为 k)")
    L.append("-" * 70)
    for lv in sorted(by_level):
        for n in by_level[lv]:
            t = by_name[n]
            d = deps[n]
            parents = ", ".join(d["internal"]) if d["internal"] else "(基础定理)"
            L.append(f"[L{lv}] {n}  ({t['file_path']}:{t['start'][0]}-{t['end'][0]})")
            L.append(f"      依赖定理: {parents}")

    L.append("")
    L.append("-" * 70)
    L.append("二、逐定理明细")
    L.append("-" * 70)
    # reverse deps (被谁依赖)
    rdeps: dict[str, set[str]] = defaultdict(set)
    for n, d in deps.items():
        for p in d["internal"]:
            rdeps[p].add(n)
    for n in order:
        t = by_name[n]
        d = deps[n]
        L.append(f"theorem {n}")
        L.append(f"  陈述: {(t['theorem_statement'] or '').strip()[:100]}")
        L.append(f"  位置: {t['file_path']} L{t['start'][0]}-{t['end'][0]}")
        if d["internal"]:
            L.append(f"  依赖定理({len(d['internal'])}): " + ", ".join(sorted(d["internal"])))
        else:
            L.append("  依赖定理: (无)")
        if d["external"]:
            L.append(f"  外部premise({len(d['external'])}):")
            for p in sorted(d["external"]):
                via = "; ".join(sorted({x[:40] for x in d["external"][p]}))
                L.append(f"    - {p}   (via: {via})")
        else:
            L.append("  外部premise: (无)")
        L.append(f"  被依赖: {', '.join(sorted(rdeps[n])) if rdeps[n] else '(无)'}")
        L.append("")

    L.append("-" * 70)
    L.append("三、边列表 (DAG edges: 依赖方 -> 被依赖方)")
    L.append("-" * 70)
    edges = [(n, p) for n in order for p in sorted(deps[n]["internal"])]
    if edges:
        L.extend(f"  {a} -> {b}" for a, b in edges)
    else:
        L.append("  (无定理间依赖边; 本数据集定理仅依赖外部premise)")
    return "\n".join(L)


# --------------- JSON output ---------------


def build_json(theorems: list[dict], deps: dict[str, dict], order: list[str],
               level: dict[str, int], inputs: list[str]) -> dict:
    """Simplified machine-readable version of the input + dependency analysis."""
    rdeps: dict[str, set[str]] = defaultdict(set)
    for n, d in deps.items():
        for p in d["internal"]:
            rdeps[p].add(n)
    by_name = {t["full_name"]: t for t in theorems}

    out = []
    for n in order:  # topological order
        t = by_name[n]
        d = deps[n]
        out.append({
            "full_name": n,
            "file_path": t["file_path"],
            "start": t["start"],
            "end": t["end"],
            "statement": t["theorem_statement"].strip(),
            "level": level[n],
            "depends_on_theorems": sorted(d["internal"]),
            "external_premises": sorted(d["external"]),
            "used_by": sorted(rdeps[n]),
        })
    return {
        "meta": {
            "inputs": inputs,
            "num_theorems": len(theorems),
            "num_internal_edges": sum(len(d["internal"]) for d in deps.values()),
            "order": "topological",
        },
        "theorems": out,
        "edges": [[n, p] for n in order for p in sorted(deps[n]["internal"])],
    }


# --------------- visualization ---------------


def draw_graph(theorems: list[dict], deps: dict[str, dict], level: dict[str, int],
               out_path: str, show_premises: bool = True) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import networkx as nx

    G = nx.DiGraph()
    max_lv = max(level.values()) if level else 0
    for t in theorems:
        n = t["full_name"]
        G.add_node(n, kind="theorem", subset=level[n])
    for n, d in deps.items():
        for p in d["internal"]:
            G.add_edge(n, p, kind="internal")
    if show_premises:
        for n, d in deps.items():
            for p in d["external"]:
                pn = f"prem::{p}"
                if pn not in G:
                    G.add_node(pn, kind="premise", subset=max_lv + 1)
                G.add_edge(n, pn, kind="external")

    pos = nx.multipartite_layout(G)  # layered left-to-right by subset
    thm_nodes = [n for n, a in G.nodes(data=True) if a["kind"] == "theorem"]
    prem_nodes = [n for n, a in G.nodes(data=True) if a["kind"] == "premise"]

    fig_w = max(12, 1.2 * (max_lv + 3))
    fig_h = max(7, 0.42 * len(G.nodes))
    fig, ax = plt.subplots(figsize=(fig_w, fig_h))

    internal_edges = [(a, b) for a, b, k in G.edges(data="kind") if k == "internal"]
    external_edges = [(a, b) for a, b, k in G.edges(data="kind") if k == "external"]
    nx.draw_networkx_edges(G, pos, edgelist=internal_edges, ax=ax,
                           edge_color="#1f77b4", width=1.4,
                           arrows=True, arrowsize=14, node_size=600)
    if external_edges:
        nx.draw_networkx_edges(G, pos, edgelist=external_edges, ax=ax,
                               edge_color="#aaaaaa", width=0.8, style="dashed",
                               arrows=True, arrowsize=8, node_size=600, alpha=0.6)
    nx.draw_networkx_nodes(G, pos, nodelist=thm_nodes, ax=ax, node_color="#4c72b0",
                           node_size=600, node_shape="o")
    if prem_nodes:
        nx.draw_networkx_nodes(G, pos, nodelist=prem_nodes, ax=ax, node_color="#c9c9c9",
                               node_size=420, node_shape="s")

    def short(n: str) -> str:
        return n if len(n) <= 30 else n[:27] + "..."
    nx.draw_networkx_labels(G, pos, ax=ax, labels={n: short(n) for n in G.nodes},
                            font_size=7)

    ax.set_title("Theorem Dependency DAG (oval=theorems, square=external premises;\n"
                 "solid=theorem deps, dashed=premise refs)")
    ax.axis("off")
    fig.tight_layout()
    fig.savefig(out_path, dpi=150)
    plt.close(fig)


# --------------- main ---------------


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("inputs", nargs="+", help="train/val/test.json 格式的文件(可多个)")
    ap.add_argument("--out", help="报告输出路径(缺省打印到终端)")
    ap.add_argument("--json", dest="json_out", help="简化版JSON输出路径")
    ap.add_argument("--graph", help="可选: 图输出路径(.png/.svg)")
    ap.add_argument("--no-premise-nodes", action="store_true",
                    help="图中不画外部premise节点(只看定理DAG)")
    args = ap.parse_args()

    theorems = load_theorems(args.inputs)
    if not theorems:
        sys.exit("没有读到任何定理,检查输入文件")
    deps = classify_deps(theorems)
    order, level, had_cycle = topo_levels(theorems, deps)

    report = build_report(theorems, deps, order, level, had_cycle, args.inputs)
    if args.out:
        Path(args.out).write_text(report)
        print(f"报告已写入: {args.out}")
    else:
        print(report)

    if args.json_out:
        payload = build_json(theorems, deps, order, level, args.inputs)
        Path(args.json_out).write_text(
            json.dumps(payload, ensure_ascii=False, indent=1)
        )
        print(f"JSON已写入: {args.json_out}")

    if args.graph:
        draw_graph(theorems, deps, level, args.graph,
                   show_premises=not args.no_premise_nodes)
        print(f"图已保存: {args.graph}")


if __name__ == "__main__":
    main()
