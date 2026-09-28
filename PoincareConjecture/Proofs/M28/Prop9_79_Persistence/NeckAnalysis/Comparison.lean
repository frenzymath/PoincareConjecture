import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.TensorNorms

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

theorem cylinderStrip_mono {epsilon eta : ℝ} (hepsilon : 0 < epsilon)
    (h : epsilon ≤ eta) : Ioo (-eta⁻¹) eta⁻¹ ⊆ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
  have hinv : eta⁻¹ ≤ epsilon⁻¹ := inv_anti₀ hepsilon h
  intro s hs
  exact ⟨(neg_le_neg hinv).trans_lt hs.1, hs.2.trans_le hinv⟩

theorem cylinderOrder_mono {epsilon eta : ℝ} (hepsilon : 0 < epsilon)
    (h : epsilon ≤ eta) : ⌊eta⁻¹⌋₊ ≤ ⌊epsilon⁻¹⌋₊ :=
  Nat.floor_mono (inv_anti₀ hepsilon h)

end PoincareConjecture.Proofs.M28.NeckAnalysis

namespace PoincareConjecture

open Proofs.M28.NeckAnalysis

theorem RoundCylinderTensorSmoothOn.mono_epsilon_m28 {epsilon eta : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn epsilon B)
    (hepsilon : 0 < epsilon) (h : epsilon ≤ eta) :
    RoundCylinderTensorSmoothOn eta B := by
  intro q a b
  apply (hB q a b).mono
  exact Set.prod_mono_right (cylinderStrip_mono hepsilon h)

theorem RoundCylinderClose.mono_epsilon_m28 {epsilon eta u : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderClose epsilon u B)
    (hepsilon : 0 < epsilon) (h : epsilon ≤ eta) (hu : u < 1) :
    RoundCylinderClose eta u B := by
  rcases hB with ⟨hsmooth, bound, hbound, hjet⟩
  refine ⟨hsmooth.mono_epsilon_m28 hepsilon h, bound,
    hbound.trans_le (sq_le_sq₀ hepsilon.le (hepsilon.le.trans h) |>.mpr h), ?_⟩
  intro z hz
  exact (roundCylinderJetErrorSquared_mono_order hu B
    (cylinderOrder_mono hepsilon h) z).trans (hjet z (cylinderStrip_mono hepsilon h hz))

theorem RoundCylinderFamilyClose.mono {epsilon eta : ℝ} {I J : Set ℝ}
    {B : ℝ → RoundCylinderTwoTensor} (hB : RoundCylinderFamilyClose epsilon I B)
    (hepsilon : 0 < epsilon) (h : epsilon ≤ eta) (hJI : J ⊆ I)
    (hJ : ∀ u ∈ J, u < 1) : RoundCylinderFamilyClose eta J B := by
  rcases hB with ⟨hsmooth, bound, hbound, hjet⟩
  refine ⟨fun u hu => (hsmooth u (hJI hu)).mono_epsilon_m28 hepsilon h, bound,
    hbound.trans_le (sq_le_sq₀ hepsilon.le (hepsilon.le.trans h) |>.mpr h), ?_⟩
  intro u hu z hz
  exact (roundCylinderJetErrorSquared_mono_order (hJ u hu) (B u)
    (cylinderOrder_mono hepsilon h) z).trans
    (hjet u (hJI hu) z (cylinderStrip_mono hepsilon h hz))

theorem exists_roundCylinderClose_perturbation_tolerance {epsilon eta : ℝ}
    (hepsilon : 0 < epsilon) (heta : epsilon < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (u : ℝ), u < 1 →
      ∀ (B C : RoundCylinderTwoTensor), RoundCylinderClose epsilon u C →
        RoundCylinderTensorSmoothOn eta B →
        (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-eta⁻¹) eta⁻¹ →
          cylinderJetDifferenceSquared u B C ⌊eta⁻¹⌋₊ z ≤ delta) →
        RoundCylinderClose eta u B := by
  have hsquare : epsilon ^ 2 < eta ^ 2 :=
    (sq_lt_sq₀ hepsilon.le (hepsilon.trans heta).le).mpr heta
  obtain ⟨theta, htheta, hgap⟩ := exists_pos_mul_lt (sub_pos.mpr hsquare) (epsilon ^ 2)
  have hremaining : 0 < eta ^ 2 - (1 + theta) * epsilon ^ 2 := by nlinarith
  obtain ⟨delta, hdelta, hbudget⟩ := exists_pos_mul_lt hremaining (1 + theta⁻¹)
  refine ⟨delta, hdelta, ?_⟩
  intro u hu B C hC hB hdifference
  rcases hC with ⟨_, bound, hbound, hjet⟩
  refine ⟨hB, (1 + theta) * bound + (1 + theta⁻¹) * delta, ?_, ?_⟩
  · have hweighted := mul_lt_mul_of_pos_left hbound (show 0 < 1 + theta by linarith)
    linarith
  · intro z hz
    apply (roundCylinderJetErrorSquared_perturbation hu B C ⌊eta⁻¹⌋₊ z htheta).trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact (roundCylinderJetErrorSquared_mono_order hu C
        (cylinderOrder_mono hepsilon heta.le) z).trans
        (hjet z (cylinderStrip_mono hepsilon heta.le hz))
    · exact mul_le_mul_of_nonneg_left (hdifference z hz) (by positivity)

end PoincareConjecture
