import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicVelocityBounds
import PoincareConjecture.Proofs.M35.RawFlow.SectionalPreservation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness



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

end PoincareConjecture.M35.Uniqueness
