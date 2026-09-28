import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Cutoff
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (F : RicciFlow n M (Iio 0))

theorem metric_inner_le_of_nonnegative_ricci
    (hRic : ∀ t < 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 0)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x v v ≤ (F.metric s).inner x v v := by
  have hm : AntitoneOn (fun t => (F.metric t).inner x v v) (Iio 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iio 0)
      (fun t ht => (F.equation t ht x v v).continuousWithinAt)
      (f' := fun t => -2 * (F.connection t).ricci x v v)
    · intro t ht
      exact (F.equation t (interior_subset ht) x v v).mono interior_subset
    · intro t ht
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (hRic t (show t ∈ Iio (0 : ℝ) from interior_subset ht) x v)
  exact hm (hst.trans_lt ht) ht hst

theorem backward_gradient_norm_le_of_nonnegative_ricci
    (hRic : ∀ t < 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 0) (f : M → ℝ) (x : M) :
    (F.metric s).tangentNorm x ((F.connection s).gradient f x) ≤
      (F.metric t).tangentNorm x ((F.connection t).gradient f x) := by
  apply ((F.connection s).gradient_norm_le_iff f x (Real.sqrt_nonneg _)).mpr
  intro v
  apply ((F.connection t).abs_mvfderiv_le_gradient_norm f x v).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt (F.metric_inner_le_of_nonnegative_ricci hRic hst ht x v)

theorem exists_backward_intrinsic_ball_cutoff [T3Space M] [PreconnectedSpace M]
    (hRic : ∀ t < 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (O : M) {α R : ℝ} (hα : 0 < α)
    (hcomplete : MetricComplete (F.metric (-α))) (hR : 1 ≤ R) :
    ∃ η : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc 0 1) ∧
      (∀ x, ((F.metric (-α)).edist O x).toReal ≤ R → η x = 1) ∧
      (tsupport η ⊆ {x | ((F.metric (-α)).edist O x).toReal ≤ 5 * R}) ∧
      ∀ τ : ℝ, α ≤ τ → ∀ x : M,
        (F.metric (-τ)).tangentNorm x ((F.connection (-τ)).gradient η x) ≤
          heatCutoffConstant / R := by
  obtain ⟨η, hη, hc, hrange, hone, hsupp, hgrad⟩ :=
    (F.connection (-α)).exists_intrinsic_ball_cutoff hcomplete O hR
  refine ⟨η, hη, hc, hrange, hone, hsupp, fun τ hτ x => ?_⟩
  apply (F.backward_gradient_norm_le_of_nonnegative_ricci hRic
    (neg_le_neg hτ) (neg_neg_of_pos hα) η x).trans
  exact (Real.sqrt_le_left (div_nonneg heatCutoffConstant_pos.le
    (zero_lt_one.trans_le hR).le)).mpr (hgrad x)

end PoincareConjecture.RicciFlow
