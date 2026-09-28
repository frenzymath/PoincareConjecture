import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetStability










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35

private theorem square_le_weighted (a b theta : ℝ) (h : 0 < theta) :
    a ^ 2 ≤ (1 + theta) * b ^ 2 + (1 + theta⁻¹) * (a - b) ^ 2 := by
  have hid : theta * ((1 + theta) * b ^ 2 + (1 + theta⁻¹) * (a - b) ^ 2 - a ^ 2) =
      (theta * b - (a - b)) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ theta *
      ((1 + theta) * b ^ 2 + (1 + theta⁻¹) * (a - b) ^ 2 - a ^ 2) := by
    rw [hid]
    exact sq_nonneg _
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left h).mp hnonneg)



theorem roundCylinderTensorNormSquared_le_weighted {u theta : ℝ}
    (hu : u < 1) (htheta : 0 < theta)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ} (T S : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) T ≤
      (1 + theta) * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) S +
      (1 + theta⁻¹) * roundCylinderTensorNormSquared u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) (fun a => T a - S a) := by
  simp only [roundCylinderTensorNormSquared_center hu, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : 0 ≤ ∏ i, ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] (a i) :=
    Finset.prod_nonneg (fun i _ => (roundCylinderInverseWeight_pos hu (a i)).le)
  convert mul_le_mul_of_nonneg_left (square_le_weighted (T a) (S a) theta htheta) hw using 1
  ring



theorem roundCylinderJetErrorSquared_le_weighted {u theta : ℝ}
    (hu : u < 1) (htheta : 0 < theta)
    (B C : RoundCylinderTwoTensor) (order : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u B order z ≤
      (1 + theta) * roundCylinderJetErrorSquared u C order z +
        (1 + theta⁻¹) * roundCylinderJetDifferenceSquared u B C order z := by
  unfold roundCylinderJetErrorSquared roundCylinderJetDifferenceSquared
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ =>
    roundCylinderTensorNormSquared_le_weighted hu htheta z.1 z.2 _ _)

end PoincareConjecture.M35

namespace PoincareConjecture.RoundCylinderFamilyClose



theorem exists_same_epsilon_perturbation_margin {epsilon : ℝ} {I : Set ℝ}
    {C : ℝ → RoundCylinderTwoTensor} (hC : RoundCylinderFamilyClose epsilon I C)
    (hI : ∀ u ∈ I, u < 1) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ B : ℝ → RoundCylinderTwoTensor,
      (∀ u ∈ I, RoundCylinderTensorSmoothOn epsilon (B u)) →
      (∀ u ∈ I, ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
        M35.roundCylinderJetDifferenceSquared u (B u) (C u) ⌊epsilon⁻¹⌋₊ z ≤ eta) →
      RoundCylinderFamilyClose epsilon I B := by
  obtain ⟨_, b, hb, hbound⟩ := hC
  have hlim : Tendsto (fun theta : ℝ => (1 + theta) * b) (𝓝[>] 0) (𝓝 b) := by
    have h : ContinuousAt (fun theta : ℝ => (1 + theta) * b) 0 := by fun_prop
    simpa only [add_zero, one_mul] using h.tendsto.mono_left nhdsWithin_le_nhds
  have hpositive : ∀ᶠ theta : ℝ in 𝓝[>] 0, 0 < theta := self_mem_nhdsWithin
  obtain ⟨theta, htheta, hmargin⟩ :=
    (hpositive.and (hlim.eventually (Iio_mem_nhds hb))).exists
  let eta := (epsilon ^ 2 - (1 + theta) * b) / (2 * (1 + theta⁻¹))
  have hden : 0 < 2 * (1 + theta⁻¹) := by positivity
  have heta : 0 < eta := div_pos (sub_pos.mpr hmargin) hden
  have heq : 2 * (1 + theta⁻¹) * eta = epsilon ^ 2 - (1 + theta) * b := by
    exact mul_div_cancel₀ _ hden.ne'
  refine ⟨eta, heta, ?_⟩
  intro B hB herr
  refine ⟨hB, (1 + theta) * b + (1 + theta⁻¹) * eta, by linarith, ?_⟩
  intro u hu z hz
  exact (M35.roundCylinderJetErrorSquared_le_weighted (hI u hu) htheta
    (B u) (C u) _ z).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hbound u hu z hz) (by positivity))
        (mul_le_mul_of_nonneg_left (herr u hu z hz) (by positivity)))

end PoincareConjecture.RoundCylinderFamilyClose
