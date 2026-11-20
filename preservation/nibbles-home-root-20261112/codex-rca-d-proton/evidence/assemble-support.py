from pathlib import Path

base = Path(__file__).resolve().parent
names = [
    "Ch08Later.lean",
    "Ch08LayerCake.lean",
    "Ch08Phi.lean",
    "Ch08Maximal.lean",
    "Ch08WeakMaximal.lean",
    "Ch08PowerLayerCake.lean",
    "Ch08StrongMaximal.lean",
    "Ch08ParameterizedMaximal.lean",
    "Ch08MaximalConstant.lean",
    "Ch08MaximalNorm.lean",
]
imports = set()
bodies = []
for name in names:
    lines = (base / name).read_text().splitlines()
    imports.update(line for line in lines if line.startswith("public import "))
    body = "\n".join(
        line for line in lines
        if line not in {"module", "public section"}
        and not line.startswith("public import ")
    )
    bodies.append(f"/- Source fragment {name} -/\n{body}")
(base / "Ch08AllSupport.lean").write_text(
    "module\n\n" + "\n".join(sorted(imports))
    + "\n\npublic section\n\n" + "\n\n".join(bodies) + "\n"
)
