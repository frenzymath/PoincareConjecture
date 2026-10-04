import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.IntrinsicVelocityBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.SectionalPreservation

/-!
# One radial velocity bound on an actual closed raw-flow slab

Morgan-Tian Section 12.6, pp. 309-314, with the corrected radial-gauge
erratum. The raw slab curvature bound and proved complete sectional
preservation supply one velocity constant for every slice. Rotation
preservation is the remaining geometric producer of the radial form.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M35.Uniqueness

/-- Every closed preterminal raw slab has one radial velocity bound,
uniform in time and on the entire intrinsic axis. -/
theorem raw_intrinsic_radial_velocity_bounded
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime) :
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : t ∈ Icc 0 T),
      ∀ hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
        ∀ x u v : StandardCapSpace,
          (G.flow.metric t).inner (standardRotation A x)
            (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
            (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) =
              (G.flow.metric t).inner x u v,
        ∀ s : ℝ, |intrinsicRadialVelocity (G.flow.metric t) hrotation
          (G.complete P ⟨ht.1, ht.2.trans_lt hTlt⟩) s| ≤ C := by
  obtain ⟨K, hK, hbound⟩ := G.curvature_locally_bounded T hT hTlt
  refine ⟨10 * (K + 1), by positivity, ?_⟩
  intro t ht hrotation s
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  exact intrinsicRadialVelocity_abs_le (G.flow.metric t) hrotation
    (G.complete P htG) (G.flow.connection t) (raw_nonnegative_sectional P G htG) hK
    (fun x => (le_abs_self _).trans (hbound t ht x)) s

end PoincareMT.M35.Uniqueness
