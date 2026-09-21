import CubeToSU3.Core
import CubeToSU3.CrossProduct
import CubeToSU3.Cube
import CubeToSU3.Anomalies
import CubeToSU3.Hexagon
import CubeToSU3.YouNian
import CubeToSU3.YouNianGray
import CubeToSU3.YouNianThreeSystems
import CubeToSU3.ClosedWalks
import CubeToSU3.Rejected
import CubeToSU3.Flavour
import CubeToSU3.CubeFlavourNoGo
import CubeToSU3.QianKunAxis
import CubeToSU3.RootMatch
import CubeToSU3.CompactSU3
import CubeToSU3.CompactSU3Real
import CubeToSU3.Weyl
import CubeToSU3.WeylReal
import CubeToSU3.SU3Group
import CubeToSU3.SU3Global
import CubeToSU3.SU3Surjectivity
import CubeToSU3.SU3SpectralStage1
import CubeToSU3.SU3SpectralStage2
import CubeToSU3.SU3SpectralStage3
import CubeToSU3.SU3SpectralStage4
import CubeToSU3.SU3SpectralStage5
import CubeToSU3.GaugeTheory
import CubeToSU3.QCDKinematics
import CubeToSU3.QCDDynamics
import CubeToSU3.GaugeGlobal
import CubeToSU3.GaugeLocal
import CubeToSU3.LatticeGauge
import CubeToSU3.LatticeNonFlat
import CubeToSU3.WilsonAction
import CubeToSU3.AnomalyLedger
import CubeToSU3.DimensionlessComparison
import CubeToSU3.PhysicsInputs
import CubeToSU3.WeightFlow

/-!
# CubeToSU3 complete import root

This root deliberately imports every source module shipped in the project.
`CubeToSU3.Check` can therefore audit the same module graph that `lake build`
builds, including the Mathlib scalar-extension, global SU(3), and classical
QCD-kinematics and dynamics layers.

The imports are listed in dependency order, grouped by layer:

* the Mathlib-free discrete layer, through `Flavour` and `CubeFlavourNoGo`;
* the 遊年 tables and their Gray-code structure;
* `QianKunAxis` and `RootMatch`, the bridge identifying the 乾-坤 diagonal's
  `Z/3` with the generator of `su(3)` and the six remaining cube vertices with
  the six roots of `A₂`;
* the algebra and group layers, with `SU3SpectralStage1`–`5` discharging the
  unitary spectral theorem that `SU3Surjectivity` used to assume;
* `GaugeTheory` (base-space free), then the classical QCD kinematics and
  dynamics, then `GaugeGlobal` and `GaugeLocal` which supply gauge covariance;
* `LatticeGauge`, `LatticeNonFlat` and `WilsonAction`, which put a lattice
  gauge theory on the cube itself, exhibit a connection carrying irremovable
  curvature, and turn that curvature into a gauge-invariant number;
* `AnomalyLedger` and `PhysicsInputs`, where the external physics assumptions
  are declared explicitly.

Diagnostic files (`Probe`, `Probe2`) are deliberately **not** imported: they
contain `sorry` and tracing options and exist only for debugging.

Lean requires every `import` command to precede this module documentation.
-/
