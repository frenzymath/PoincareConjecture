import PoincareLib.Geometry.RicciFlow.AncientKappa.Rescaling.Setup
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Theory
import PoincareLib.Geometry.RicciFlow.Rescaling.Theory

/-!
# M17 source-specific blow-up sequence statement

The public conclusion is parameterized by the ancient solution, a fixed
reference point, and an arbitrary positive scale sequence tending to infinity.
The reduced-volume provider supplies the source minimum bound at every finite
horizon; the M13 provider supplies the actual positive parabolic rescaling.
No limit, subsequence extraction, bounded-distance estimate, AVR statement, or
soliton equation is included here.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-! The uniform form of the already-proved M10 minimum-bound output used by
M17.  Each provider value is instantiated at a horizon larger than the
requested scale, so the strict finite-horizon hypothesis is respected. -/
def AncientReducedVolumeMinimumProvider
    (K : AncientKappaSolution n M) : Prop :=
  ∀ R : ℝ, 0 < R → Nonempty (ReducedVolumeTheory K.flow 0 R)

/-! The exact M17 output for the prescribed scale sequence. -/
def AncientBlowupSetupConclusion
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ) : Prop :=
  Nonempty (AncientBlowupSetup K reference tau)

/-! A theorem-shaped package for all fixed-carrier inputs in dimension `n`.
The checked assembly in `Proofs/M17.lean` supplies the predecessor services
once; each application takes only the prescribed geometric inputs. -/
structure AncientBlowupSetupTheory (n : ℕ) : Prop where
  setup : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ),
    (tau_pos : ∀ k, 0 < tau k) →
    (tau_tendsto : Filter.Tendsto tau Filter.atTop Filter.atTop) →
    AncientBlowupSetupConclusion K reference tau

end PoincareMT
