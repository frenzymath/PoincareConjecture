import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic
import PoincareLib.Geometry.RicciFlow.AncientKappa.Rescaling.SetupTheory
import PoincareLib.Geometry.RicciFlow.AncientKappa.Theory
import PoincareLib.Geometry.RicciFlow.Harnack.Theory
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Theory
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Theory

/-!
# M18 source-specific asymptotic soliton statement

Morgan--Tian Theorem 9.11 is dimension-general.  Its input is an actual
fixed-carrier sequence of ordinary rescalings and reduced-length minimisers;
the output is a pointed smooth limit on the open ancient interval.  The
predecessor bundle below exposes the finite-window structural estimates,
Harnack, L-geometry, reduced-length/reduced-volume, and pointed-compactness
services used in the proof.  It does not contain a limit witness.

The generic varying-carrier blow-up and bounded-distance interfaces belong to
M29--M30.  Remark 9.12 also excludes bounded-curvature time slices and a
global one-parameter self-similarity family from this milestone.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-! The direct predecessor services for the actual sequence. -/
structure AncientAsymptoticSolitonPredecessors
    (K : AncientKappaSolution n M) : Prop where
  structural : AncientKappaStructuralConclusion.{u} n
  harnack : HarnackAncientTheory.{u}
  pointed_compactness :
    ∀ {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses n T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  l_geometry : ∀ R : ℝ, 0 < R →
    Nonempty (LGeodesicTheory K.flow 0 R)
  reduced_length : ∀ R : ℝ, 0 < R →
    Nonempty (ReducedLengthDifferentialTheory K.flow 0 R)
  reduced_volume : ∀ R : ℝ, 0 < R →
    Nonempty (ReducedVolumeTheory K.flow 0 R)

/-! A limit of the specified rescaling sequence. M17 constructs such a
sequence; its reference, scales and minimizing points are intrinsic fields.
The checked setup adapter in `Proofs/M18.lean` preserves this exact input. -/
def AncientAsymptoticSolitonConclusion
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K) : Prop :=
  Nonempty (AncientAsymptoticSolitonLimitData S)

/-! The dimension-general all-sequence service exposed to later
classification milestones. The checked assembly captures the earlier
services, so a caller supplies only an actual source sequence. -/
structure AncientAsymptoticSolitonTheory (n : ℕ) : Prop where
  limits : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (S : AncientRescalingSequence K),
    AncientAsymptoticSolitonConclusion S

end PoincareMT
