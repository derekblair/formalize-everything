from pathlib import Path
import hashlib, json

base = Path(__file__).resolve().parent
sources = [
    'InfinityBridge.lean', 'RationalPartialFractions.lean', 'StripComponents.lean',
    'BalancedCycles.lean', 'Exhaustion.lean', 'PolynomialObstruction.lean',
    'SquareKernel.lean', 'HolomorphicLog.lean', 'PrimitiveLog.lean',
    'RungeFunctional.lean', 'GridBoundary.lean',
    'ContourContinuity.lean', 'SegmentIntegralBridge.lean', 'PolygonalConcat.lean',
    'CyclicVertices.lean', 'SimplyConnectedImplications.lean', 'PrimitiveCurveIntegral.lean',
    'CauchyTransformSphere.lean', 'ContourAnnihilator.lean',
    'RungeRationalWitness.lean', 'RungePolynomialWitness.lean',
    'RungeAssembly.lean', 'RungeUniformSequences.lean',
    'GridGeometry.lean', 'GridSupport.lean',
    'OffGridDensity.lean', 'GridIntegral.lean', 'GridCauchy.lean', 'GridRepresentation.lean',
    'OpenRungeAssembly.lean',
    'MittagLefflerCore.lean', 'MittagLefflerSeries.lean', 'MittagLefflerAssembly.lean',
    'PolygonalCyclePackage.lean', 'PolygonalRegularity.lean', 'PolygonalCauchyFormula.lean',
    'SphericalSeparation.lean', 'CycleSeparation.lean', 'PolygonalCycleSeparation.lean',
    'PolygonalPrimitives.lean', 'PolynomialApproximationCurve.lean',
    'RungeNecessityException.lean', 'RationalObstruction.lean',
    'RiemannUnitDiscShift.lean', 'RiemannInitialMap.lean', 'RiemannHurwitz.lean',
    'RiemannMappingFull.lean', 'RiemannMappingSquareRoots.lean', 'RiemannHomeomorphism.lean',
]
imports = []
sections = []
metadata = []
for i, name in enumerate(sources):
    text = (base / name).read_text()
    lines = []
    for line in text.splitlines():
        if line.startswith('import '):
            if line not in imports:
                imports.append(line)
        elif line == 'noncomputable section':
            continue
        else:
            lines.append(line)
    sections.append((name, '\n'.join(lines)))
    metadata.append({'source': name, 'sha256': hashlib.sha256(text.encode()).hexdigest()})
output = '\n'.join(imports) + '\n\nset_option autoImplicit false\n\n'
for i, (name, body) in enumerate(sections):
    output += f'/- Source: {name} -/\nnoncomputable section Source{i}\n'
    metadata[i]['body_first_line'] = output.count('\n') + 1
    output += body + f'\nend Source{i}\n\n'
    metadata[i]['section_last_line'] = output.count('\n')
(base / 'AllPending.lean').write_text(output)
(base / 'all-pending-sources.json').write_text(json.dumps(metadata, indent=2) + '\n')
print(f'Aggregate: {len(sources)} sources, {output.count(chr(10))} lines, {len(imports)} imports.')
