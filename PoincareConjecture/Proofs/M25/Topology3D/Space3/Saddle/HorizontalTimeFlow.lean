import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow











set_option autoImplicit false

open Set
open scoped ContDiff NNReal Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (v : ℝ → ℝ) {K L : ℝ≥0}
variable (hK : LipschitzWith K v) (hL : ∀ z, ‖v z‖ ≤ L)
variable (hv : ContDiff ℝ ∞ v) (hs : HasCompactSupport v)
variable (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ)




noncomputable def horizontalTimeFlowDiffeomorph (t : ℝ) :
    Diffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ := by
  let F (s : ℝ) (p : E × ℝ) := (p.1, boundedFlow v hK hL p.2 (χ p.1 * s))
  have hF (s : ℝ) : ContDiff ℝ ∞ (F s) :=
    contDiff_fst.prodMk ((boundedFlow_contDiff v hK hL hv hs).comp
      (contDiff_snd.prodMk ((hχ.comp contDiff_fst).mul contDiff_const)))
  exact {
    toEquiv := {
      toFun := F t
      invFun := F (-t)
      left_inv := by
        intro p
        apply Prod.ext
        · rfl
        · simpa only [F, mul_neg] using boundedFlow_neg v hK hL p.2 (χ p.1 * t)
      right_inv := by
        intro p
        apply Prod.ext
        · rfl
        · simpa only [F, mul_neg, neg_neg] using
            boundedFlow_neg v hK hL p.2 (χ p.1 * (-t)) }
    contMDiff_toFun := (hF t).contMDiff
    contMDiff_invFun := (hF (-t)).contMDiff }



theorem horizontalTimeFlowDiffeomorph_apply (t : ℝ) (p : E × ℝ) :
    horizontalTimeFlowDiffeomorph v hK hL hv hs χ hχ t p =
      (p.1, boundedFlow v hK hL p.2 (χ p.1 * t)) := rfl



theorem horizontalTimeFlowDiffeomorph_symm_apply (t : ℝ) (p : E × ℝ) :
    (horizontalTimeFlowDiffeomorph v hK hL hv hs χ hχ t).symm p =
      (p.1, boundedFlow v hK hL p.2 (χ p.1 * (-t))) := rfl



theorem horizontalTimeFlowDiffeomorph_contDiff : ContDiff ℝ ∞
    (fun p : ℝ × (E × ℝ) => horizontalTimeFlowDiffeomorph v hK hL hv hs χ hχ p.1 p.2) :=
  contDiff_snd.fst.prodMk ((boundedFlow_contDiff v hK hL hv hs).comp
    (contDiff_snd.snd.prodMk ((hχ.comp contDiff_snd.fst).mul contDiff_fst)))




theorem horizontalTimeFlowDiffeomorph_tsupport_subset (t : ℝ) :
    tsupport (fun p => horizontalTimeFlowDiffeomorph v hK hL hv hs χ hχ t p - p) ⊆
      tsupport χ ×ˢ tsupport v := by
  apply closure_minimal ?_ ((isClosed_tsupport χ).prod (isClosed_tsupport v))
  intro p hp
  constructor
  · by_contra hx
    have hχzero : χ p.1 = 0 := image_eq_zero_of_notMem_tsupport hx
    have hfix : horizontalTimeFlowDiffeomorph v hK hL hv hs χ hχ t p = p := by
      apply Prod.ext
      · rfl
      · change boundedFlow v hK hL p.2 (χ p.1 * t) = p.2
        rw [hχzero, zero_mul, boundedFlow_zero]
    exact hp (sub_eq_zero.mpr hfix)
  · by_contra hz
    have hvzero : v p.2 = 0 := image_eq_zero_of_notMem_tsupport hz
    have hfix : horizontalTimeFlowDiffeomorph v hK hL hv hs χ hχ t p = p := by
      apply Prod.ext
      · rfl
      · exact boundedFlow_eq_self v hK hL p.2 hvzero (χ p.1 * t)
    exact hp (sub_eq_zero.mpr hfix)

end PoincareConjecture.M25.Topology3D
