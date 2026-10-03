"""
Example script for generating dataset from a local Lean 4 repository. 
The data is saved at <RAID_DIR>/<DATA_DIR>/<repo.name>_<repo.commit>.
e.g. LeanDojo-v2/raid/data/lean4-example_3e23ab0bfdcfdbd5b11ab53c2cd8b5d16492e9c2

Usage: python examples/data_generation/trace_local.py
"""

from lean_dojo_v2.database import DynamicDatabase


def main() -> None:
    path = "/home/yangronghui/projects/LeanDojo-v2/examples/data_generation/cslib"
    commit = "c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5"

    database = DynamicDatabase()

    database.trace_repository(
        url=path,
        commit=commit,
        build_deps=False,
    )


if __name__ == "__main__":
    main()
