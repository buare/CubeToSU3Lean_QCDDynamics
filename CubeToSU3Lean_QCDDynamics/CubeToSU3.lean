import CubeToSU3.Core
import CubeToSU3.CrossProduct
import CubeToSU3.Cube
import CubeToSU3.Anomalies
import CubeToSU3.Rejected
import CubeToSU3.Hexagon
import CubeToSU3.YouNian
import CubeToSU3.ClosedWalks
import CubeToSU3.Flavour
import CubeToSU3.CompactSU3
import CubeToSU3.CompactSU3Real
import CubeToSU3.Weyl
import CubeToSU3.WeylReal
import CubeToSU3.SU3Group
import CubeToSU3.SU3Global
import CubeToSU3.SU3Surjectivity
import CubeToSU3.QCDKinematics
import CubeToSU3.QCDDynamics
import CubeToSU3.DimensionlessComparison
import CubeToSU3.PhysicsInputs
import CubeToSU3.CG.Baryon
import CubeToSU3.CG.BCJ
import CubeToSU3.CG.SpringRing
import CubeToSU3.CG.HuckelRing
import CubeToSU3.QianKunAxis
import CubeToSU3.RootMatch
import CubeToSU3.QianKunStabilizer
/-!
# CubeToSU3 complete import root

This root deliberately imports every source module shipped in the project.
`CubeToSU3.Check` can therefore audit the same module graph that `lake build`
builds, including the Mathlib scalar-extension, global SU(3), and classical
QCD-kinematics and dynamics layers.

Lean requires every `import` command to precede this module documentation.
-/
