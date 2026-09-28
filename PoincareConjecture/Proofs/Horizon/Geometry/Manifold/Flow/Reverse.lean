import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Uniqueness







open Set Filter
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Poincare.Manifold

theorem reverse_integralCurve_endpoint
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {X : (x : M) → TangentSpace (𝓡 n) x} {U : Set M} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U)
    {α β : ℝ → M} {T δ ε : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hε : 0 < ε)
    (hαU : ∀ t ∈ Ioo (-δ) (T + δ), α t ∈ U)
    (hα : IsMIntegralCurveOn (I := 𝓡 n) α X (Ioo (-δ) (T + δ)))
    (hβ : IsMIntegralCurveOn (I := 𝓡 n) β (fun x => -X x) (Ioo (-ε) (T + ε)))
    (hinit : α T = β 0) : β T = α 0 := by
  let d := min δ ε
  have hd : 0 < d := lt_min hδ hε
  have hdδ : d ≤ δ := min_le_left _ _
  have hdε : d ≤ ε := min_le_right _ _
  have hsub : Ioo (-d) (T + d) ⊆ Ioo (-δ) (T + δ) := by
    apply Ioo_subset_Ioo <;> linarith
  have hrev : IsMIntegralCurveOn (I := 𝓡 n) (fun t => β (T-t)) X
      (Ioo (-d) (T+d)) := by
    have hr := ((hβ.comp_add T).comp_mul (-1)).mono
      (show Ioo (-d) (T+d) ⊆ {t : ℝ | t * -1 + T ∈ Ioo (-ε) (T+ε)} from by
        intro t ht
        constructor <;> linarith [ht.1,ht.2])
    simpa only [Function.comp_def, Pi.smul_apply, neg_one_smul, neg_neg,
      mul_neg_one, neg_add_eq_sub, Pi.neg_def] using hr
  have heq := eqOn_of_isMIntegralCurveOn hU hX isOpen_Ioo isPreconnected_Ioo
    (show T ∈ Ioo (-d) (T+d) from ⟨by linarith,by linarith⟩)
    (fun t ht => hαU t (hsub ht)) (hα.mono hsub) hrev
    (by simpa only [sub_self] using hinit)
  simpa only [sub_zero] using (heq (show 0 ∈ Ioo (-d) (T+d) from ⟨by linarith,by linarith⟩)).symm
end Poincare.Manifold
