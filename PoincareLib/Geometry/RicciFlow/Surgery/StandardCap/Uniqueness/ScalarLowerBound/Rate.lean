import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceData
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Mathlib.UniformReciprocalRate

/-!
# The scalar-rate assembly on the supplied standard flow

Morgan-Tian, Proposition 12.31, printed pp. 325-326, with the corrected
reciprocal argument. This lemma uses the actual metric and connection of E.
The uniform high-curvature estimate, pointwise blowup and early positive
floors remain geometric obligations; they are not consequences of ODE alone.
-/

set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Proposition 12.31, pp. 325-326: M04 scalar evolution converts the guarded geometric
estimate and blowup into one positive coefficient valid on the actual E. -/
theorem scalar_lower_rate_of_blowup_and_guarded_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (hfloor : ∀ T ∈ Ico 0 E.flow.base.lifetime,
      ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace,
        B ≤ (E.flow.connection t).scalarCurvature x)
    (hblow : ∀ x : StandardCapSpace,
      Tendsto (fun t => (E.flow.connection t).scalarCurvature x) (𝓝[<] 1) atTop)
    (hbound : ∃ A H : ℝ, 0 < A ∧ 0 < H ∧
      ∀ t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
        H ≤ (E.flow.connection t).scalarCurvature x →
        (E.flow.connection t).laplacian (E.flow.connection t).scalarCurvature x +
          2 * (E.flow.connection t).ricciNormSq x ≤
            A * ((E.flow.connection t).scalarCurvature x) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
      c / (1 - t) ≤ (E.flow.connection t).scalarCurvature x := by
  obtain ⟨A, H, hA, hH, hguard⟩ := hbound
  have htime {t : ℝ} (ht : t ∈ Ico 0 1) : t ∈ Ico 0 E.flow.base.lifetime := by
    simpa only [E.lifetime_one] using ht
  have hpos (x : StandardCapSpace) (t : ℝ) (ht : t ∈ Ico 0 1) :
      0 < (E.flow.connection t).scalarCurvature x := by
    obtain ⟨B, hB, hBt⟩ := hfloor t (htime ht)
    exact hB.trans_le (hBt t ⟨ht.1, le_rfl⟩ x)
  obtain ⟨τ, hτ, hτhalf, hfinal⟩ := exists_uniform_final_reciprocal_bound hA hH hpos
    (fun x t ht => (P.scalar_evolution 3 StandardCapSpace _ E.flow.base.flow
      t (htime ht) x).mono (fun _ hs => htime hs))
    (fun x t ht => hguard t (htime ht) x) hblow
  have hearlyTime : 1 - τ ∈ Ico 0 E.flow.base.lifetime := by
    apply htime
    constructor <;> linarith
  obtain ⟨B, hB, hearly⟩ := hfloor (1 - τ) hearlyTime
  obtain ⟨c, hc, hrate⟩ := exists_uniform_reciprocal_bound_of_early_floor hA hB hτ
    (fun x t ht => hearly t ht x) hfinal
  refine ⟨c, hc, ?_⟩
  intro t ht x
  exact hrate x t (by simpa only [E.lifetime_one] using ht)

end PoincareMT.RepairedStandardCapExistenceData
