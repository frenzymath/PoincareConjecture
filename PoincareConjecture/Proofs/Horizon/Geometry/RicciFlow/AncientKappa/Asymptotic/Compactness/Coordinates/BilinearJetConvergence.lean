import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.BilinearJets
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LocalConvergence






set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem tendstoUniformlyOn_bilinear_jets_of_basis_entries
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {A : ℕ → E → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {B : E → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hA : ∀ᶠ k in atTop, ∀ x ∈ K, ContDiffAt ℝ ∞ (A k) x)
    (hB : ∀ x ∈ K, ContDiffAt ℝ ∞ B x) (m : ℕ)
    (hentry : ∀ i j : Fin n, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun x => A k x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)))
      (iteratedFDeriv ℝ m (fun x => B x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)))
      atTop K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (A k)) (iteratedFDeriv ℝ m B) atTop K := by
  apply (Metric.tendstoUniformlyOn_iff
    (F := fun k => iteratedFDeriv ℝ m (A k)) (f := iteratedFDeriv ℝ m B)).mpr
  intro ε hε
  let δ := ε / ((n : ℝ) ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hm : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  have he : ∀ᶠ k in atTop, ∀ i j : Fin n, ∀ x ∈ K,
      dist (iteratedFDeriv ℝ m (fun y => B y
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x)
        (iteratedFDeriv ℝ m (fun y => A k y
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x) < δ :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun j =>
      Metric.tendstoUniformlyOn_iff.mp (hentry i j) δ hδ))
  filter_upwards [hA, he] with k hk he x hx
  have hb := hB x hx
  have ha := hk x hx
  have hbound := norm_iteratedFDeriv_bilinear_le_of_entries (hb.sub ha) m hδ.le
    (fun i j => ?_)
  · rw [dist_eq_norm (iteratedFDeriv ℝ m B x) (iteratedFDeriv ℝ m (A k) x),
      ← iteratedFDeriv_sub_apply (hb.of_le hm) (ha.of_le hm)]
    apply hbound.trans_lt
    calc (n : ℝ) ^ 2 * δ < ((n : ℝ) ^ 2 + 1) * δ :=
          mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := mul_div_cancel₀ ε (by positivity)
  · let L : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).comp
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (EuclideanSpace.basisFun (Fin n) ℝ i))
    have hBs : ContDiffAt ℝ ∞ (fun y => L (B y)) x :=
      (hb.clm_apply contDiffAt_const).clm_apply contDiffAt_const
    have hAs : ContDiffAt ℝ ∞ (fun y => L (A k y)) x :=
      (ha.clm_apply contDiffAt_const).clm_apply contDiffAt_const
    change ‖iteratedFDeriv ℝ m (fun y => L ((B - A k) y)) x‖ ≤ δ
    have hf : (fun y => L ((B - A k) y)) = (fun y => L (B y)) - (fun y => L (A k y)) := by
      ext y
      exact L.map_sub (B y) (A k y)
    rw [hf, iteratedFDeriv_sub_apply (hBs.of_le hm) (hAs.of_le hm)]
    simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      dist_eq_norm] using (le_of_lt (he i j x hx) : dist _ _ ≤ δ)

end Poincare.Analysis.Calculus
