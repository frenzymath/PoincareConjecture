import PoincareConjecture.Proofs.M25.Topology3D.Space3.AffineFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowFirstIntegral

set_option autoImplicit false

open Set
open scoped NNReal ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem scalarFlow_eq_add_on (b : ℝ → ℝ) {K L : ℝ≥0}
    (hK : LipschitzWith K b) (hL : ∀ z, ‖b z‖ ≤ L)
    (m : ℝ) {d : ℝ} (hd : 0 < d)
    (hb : ∀ z ∈ Ioo (m - d) (m + d), b z = 1) {t : ℝ}
    (ht : t ∈ Ioo (-d) d) : boundedFlow b hK hL m t = m + t := by
  have heq := boundedFlow_eq_affine_on b hK hL 1 m hd (by
    intro u hu
    simp only [smul_eq_mul, mul_one]
    exact hb (m + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩) ht
  simpa only [smul_eq_mul, mul_one] using heq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (f : E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
variable (b : ℝ → ℝ) {Kb Lb : ℝ≥0}
variable (hbK : LipschitzWith Kb b) (hbL : ∀ z, ‖b z‖ ≤ Lb)
variable {S : Set E} (H : E → ℝ)
variable (hH : ∀ x ∈ S, DifferentiableAt ℝ H x)
variable (hHb : ∀ x ∈ S, fderiv ℝ H x (f x) = b (H x))
variable (hS : ∀ x ∈ S, ∀ t, boundedFlow f hK hL x t ∈ S)
variable (m : ℝ) {d : ℝ} (hd : 0 < d)
variable (hb : ∀ z ∈ Ioo (m - d) (m + d), b z = 1)

include hbK hbL hH hHb hS hd hb

theorem regularFlow_height {x : E} (hx : x ∈ S) (hxm : H x = m)
    {t : ℝ} (ht : t ∈ Ioo (-d) d) :
    H (boundedFlow f hK hL x t) = m + t := by
  rw [boundedFlow_intertwines_on f hK hL b hbK hbL H hH hHb x (hS x hx), hxm]
  exact scalarFlow_eq_add_on b hbK hbL m hd hb ht

theorem regularFlow_back_height {y : E} (hy : y ∈ S)
    (hyH : H y ∈ Ioo (m - d) (m + d)) :
    H (boundedFlow f hK hL y (m - H y)) = m := by
  have ht : H y - m ∈ Ioo (-d) d := ⟨by linarith [hyH.1], by linarith [hyH.2]⟩
  have heq := scalarFlow_eq_add_on b hbK hbL m hd hb ht
  have heq' : boundedFlow b hbK hbL m (H y - m) = H y := by
    calc
      _ = m + (H y - m) := heq
      _ = H y := by ring
  rw [boundedFlow_intertwines_on f hK hL b hbK hbL H hH hHb y (hS y hy)]
  calc
    _ = boundedFlow b hbK hbL (boundedFlow b hbK hbL m (H y - m)) (m - H y) := by
      rw [heq']
    _ = m := by
      rw [show m - H y = -(H y - m) by ring, boundedFlow_neg]

noncomputable def regularLevelEquiv :
    ({x : E // x ∈ S ∧ H x = m} × Ioo (-d) d) ≃
      {y : E // y ∈ S ∧ H y ∈ Ioo (m - d) (m + d)} where
  toFun p := ⟨boundedFlow f hK hL p.1.1 p.2.1, hS p.1.1 p.1.2.1 p.2.1, by
    rw [regularFlow_height f hK hL b hbK hbL H hH hHb hS m hd hb
      p.1.2.1 p.1.2.2 p.2.2]
    exact ⟨by linarith [p.2.2.1], by linarith [p.2.2.2]⟩⟩
  invFun y := (⟨boundedFlow f hK hL y.1 (m - H y.1), hS y.1 y.2.1 _,
    regularFlow_back_height f hK hL b hbK hbL H hH hHb hS m hd hb y.2.1 y.2.2⟩,
    ⟨H y.1 - m, by constructor <;> linarith [y.2.2.1, y.2.2.2]⟩)
  left_inv p := by
    have heq := regularFlow_height f hK hL b hbK hbL H hH hHb hS m hd hb
      p.1.2.1 p.1.2.2 p.2.2
    apply Prod.ext
    · apply Subtype.ext
      change boundedFlow f hK hL (boundedFlow f hK hL p.1.1 p.2.1)
        (m - H (boundedFlow f hK hL p.1.1 p.2.1)) = p.1.1
      rw [heq, show m - (m + p.2.1) = -p.2.1 by ring, boundedFlow_neg]
    · apply Subtype.ext
      change H (boundedFlow f hK hL p.1.1 p.2.1) - m = p.2.1
      rw [heq]
      ring
  right_inv y := by
    apply Subtype.ext
    change boundedFlow f hK hL (boundedFlow f hK hL y.1 (m - H y.1))
      (H y.1 - m) = y.1
    rw [← boundedFlow_add, show m - H y.1 + (H y.1 - m) = 0 by ring, boundedFlow_zero]

@[simp] theorem regularLevelEquiv_apply
    (p : {x : E // x ∈ S ∧ H x = m} × Ioo (-d) d) :
    (regularLevelEquiv f hK hL b hbK hbL H hH hHb hS m hd hb p).1 =
      boundedFlow f hK hL p.1.1 p.2.1 := rfl

@[simp] theorem regularLevelEquiv_symm_apply
    (y : {y : E // y ∈ S ∧ H y ∈ Ioo (m - d) (m + d)}) :
    ((regularLevelEquiv f hK hL b hbK hbL H hH hHb hS m hd hb).symm y).1.1 =
      boundedFlow f hK hL y.1 (m - H y.1) := rfl

noncomputable def regularLevelHomeomorph [FiniteDimensional ℝ E]
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ({x : E // x ∈ S ∧ H x = m} × Ioo (-d) d) ≃ₜ
      {y : E // y ∈ S ∧ H y ∈ Ioo (m - d) (m + d)} where
  toEquiv := regularLevelEquiv f hK hL b hbK hbL H hH hHb hS m hd hb
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (boundedFlow_contDiff f hK hL hf hs).continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    have hheight : Continuous
        (fun y : {y : E // y ∈ S ∧ H y ∈ Ioo (m - d) (m + d)} => H y.1) :=
      continuousOn_iff_continuous_domRestrict.mp
        (fun y hy => (hH y hy.1).continuousAt.continuousWithinAt)
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (boundedFlow_contDiff f hK hL hf hs).continuous.comp
        (continuous_subtype_val.prodMk (continuous_const.sub hheight))
    · exact (hheight.sub continuous_const).subtype_mk _

omit hbK hbL hH hHb hS hd hb in

theorem regularFlow_back_contDiffOn [FiniteDimensional ℝ E]
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    {U : Set E} (hHU : ContDiffOn ℝ ∞ H U) :
    ContDiffOn ℝ ∞ (fun y =>
      (boundedFlow f hK hL y (m - H y), H y - m)) U := by
  exact ((boundedFlow_contDiff f hK hL hf hs).comp_contDiffOn
    (contDiffOn_id.prodMk (contDiffOn_const.sub hHU))).prodMk
    (hHU.sub contDiffOn_const)

end PoincareConjecture.M25.Topology3D
