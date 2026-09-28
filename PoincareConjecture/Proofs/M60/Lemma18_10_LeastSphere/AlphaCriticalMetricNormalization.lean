import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessBounds
import Mathlib.LinearAlgebra.QuadraticForm.Real










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter ContinuousLinearMap
open scoped Topology InnerProductSpace

noncomputable section

namespace PoincareConjecture.M60

local instance suMetricNormalizationBilinearGroup {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance suMetricNormalizationBilinearSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace



theorem suPositiveMetric_linear_normalization {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ v w, B v w = inner ℝ (L v) (L w) := by
  let E := EuclideanSpace ℝ (Fin n)
  let Q : QuadraticForm ℝ E := B.toBilinForm.toQuadraticMap
  have hQ : ∃ w : Fin n → ℝ, (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) := by
    have hdim : Module.finrank ℝ E = n := by simp [E]
    have hraw := Q.equivalent_one_zero_neg_one_weighted_sum_squared
    rw [hdim] at hraw
    exact hraw
  obtain ⟨w, hw, ⟨e⟩⟩ := hQ
  have hw1 (i : Fin n) : w i = 1 := by
    let v := e.symm (Pi.single i (1 : ℝ))
    have hv : v ≠ 0 := by
      intro hv
      have h := congrArg e hv
      have hi := congrFun h i
      simp [v] at hi
    have hpos := hp v hv
    have he := e.map_app v
    have hdiag : w i = B v v := by
      simp only [QuadraticMap.weightedSumSquares_apply, Q,
        LinearMap.BilinMap.toQuadraticMap_apply, toBilinForm_apply] at he
      simpa [v, Pi.single_apply, Finset.sum_ite_eq'] using he
    rcases hw i with h | h | h
    · rw [← hdiag, h] at hpos
      linarith
    · rw [← hdiag, h] at hpos
      linarith
    · exact h
  let L : E ≃L[ℝ] E :=
    (e.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm).toContinuousLinearEquiv
  have hdiag (v : E) : B v v = ‖L v‖ ^ 2 := by
    have he := e.map_app v
    simp only [QuadraticMap.weightedSumSquares_apply, Q,
      LinearMap.BilinMap.toQuadraticMap_apply, toBilinForm_apply, hw1, one_smul] at he
    rw [EuclideanSpace.real_norm_sq_eq]
    have hLv (i : Fin n) : L v i = e v i := rfl
    simpa only [hLv, pow_two] using he.symm
  refine ⟨L, fun v w => ?_⟩
  have hv := hdiag v
  have hw := hdiag w
  have hvw := hdiag (v + w)
  simp only [map_add, add_apply, hs w v, norm_add_sq_real] at hvw
  linarith




theorem suContinuousMetric_local_normalization {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (hB : ContinuousAt B y)
    (hs : ∀ v w, B y v w = B y w v) (hp : ∀ v, v ≠ 0 → 0 < B y v v) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ v w, B y v w = inner ℝ (L v) (L w)) ∧
      ∀ᶠ z in 𝓝 y,
        ‖(B z).bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap‖ ≤ 2 ∧
        ∀ v, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
          (B z).bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap v v := by
  obtain ⟨L, hL⟩ := suPositiveMetric_linear_normalization (B y) hs hp
  let C := fun z => (B z).bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  have hC : ContinuousAt C y := by
    apply continuousAt_clm_apply.mpr
    intro v
    apply continuousAt_clm_apply.mpr
    intro w
    exact (hB.clm_apply continuousAt_const).clm_apply continuousAt_const
  let I : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  have hCy : C y = I := by
    ext v w
    change B y (L.symm v) (L.symm w) = inner ℝ v w
    rw [hL, L.apply_symm_apply, L.apply_symm_apply]
  refine ⟨L, hL, ?_⟩
  filter_upwards [Metric.tendsto_nhds.mp hC (1 / 2) (by norm_num)] with z hz
  rw [dist_eq_norm, hCy] at hz
  constructor
  · have hi := norm_innerSL_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
    have hn := norm_le_norm_sub_add (C z) I
    change ‖C z‖ ≤ 2
    linarith
  · intro v
    have he := (C z - I).le_opNorm₂ v v
    have he' : |C z v v - ‖v‖ ^ 2| ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖C z - I‖ * ‖v‖ * ‖v‖ := by
          change |C z v v - inner ℝ v v| ≤ _ at he
          simpa only [real_inner_self_eq_norm_sq] using he
        _ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
    change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ C z v v
    linarith [neg_le_of_abs_le he']



theorem suAlphaHessianTerm_linear_change {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : Fin 2 → EuclideanSpace ℝ (Fin n))
    (H : Fin 2 → Fin 2 → EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    L (suAlphaHessianTerm B v H d) =
      suAlphaHessianTerm (B.bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap)
        (fun i => L (v i)) (fun i j => L (H i j)) d := by
  simp only [suAlphaHessianTerm, map_smul, map_sum, bilinearComp_apply,
    ContinuousLinearEquiv.coe_apply, L.symm_apply_apply]




theorem suAlphaHessianTerm_transformed_bound {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : Fin 2 → EuclideanSpace ℝ (Fin n))
    (H : Fin 2 → Fin 2 → EuclideanSpace ℝ (Fin n)) {d : ℝ}
    (hd : 0 < d)
    (hB : ‖B.bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap‖ ≤ 2)
    (hc : ∀ w, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤
      B.bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap w w)
    (hden : (∑ i : Fin 2, B (v i) (v i)) ≤ d) :
    ‖L (suAlphaHessianTerm B v H d)‖ ≤
      16 * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖L (H i j)‖ ^ 2) := by
  rw [suAlphaHessianTerm_linear_change]
  have h := suAlphaHessianTerm_bound
    (B.bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap)
    (fun i => L (v i)) (fun i j => L (H i j)) hd (by norm_num : (0 : ℝ) < 1 / 2) hB hc
    (by simpa only [bilinearComp_apply, ContinuousLinearEquiv.coe_apply, L.symm_apply_apply]
      using hden)
  norm_num at h ⊢
  exact h

end PoincareConjecture.M60

end
