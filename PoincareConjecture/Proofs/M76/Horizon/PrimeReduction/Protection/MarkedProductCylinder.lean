import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCylinderRim
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentFiniteModel




noncomputable section

open Set Metric BrownCollar

namespace PoincareConjecture.M76

variable {κ : Type*} [Fintype κ] [Unique κ]

def markedIntervalBallCoordinates :
    Icc (0 : ℝ) 1 ≃ₜ closedBall (0 : κ → ℝ) (3 / 2) where
  toFun t := ⟨fun _ => 3 * (t : ℝ) - 3 / 2, by
    rw [mem_closedBall_zero_iff, pi_norm_const, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun x := ⟨(x.val default + 3 / 2) / 3, by
    have hn := abs_le.mp ((norm_le_pi_norm x.val default).trans
      (mem_closedBall_zero_iff.mp x.property))
    constructor <;> linarith [hn.1, hn.2]⟩
  left_inv t := by
    apply Subtype.ext
    change (3 * (t : ℝ) - 3 / 2 + 3 / 2) / 3 = t
    ring
  right_inv x := by
    apply Subtype.ext
    funext k
    change 3 * ((x.val default + 3 / 2) / 3) - 3 / 2 = x.val k
    rw [show default = k from Subsingleton.elim _ _]
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply default).comp continuous_subtype_val).add
      continuous_const).div_const 3

theorem markedIntervalBallCoordinates_rim (t : Icc (0 : ℝ) 1) :
    (markedIntervalBallCoordinates (κ := κ) t : κ → ℝ) ∈ sphere 0 (3 / 2) ↔
      (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
  change (fun _ : κ => 3 * (t : ℝ) - 3 / 2) ∈ sphere 0 (3 / 2) ↔ _
  rw [mem_sphere_zero_iff_norm, pi_norm_const, Real.norm_eq_abs]
  rw [abs_eq (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; rw [h]; norm_num
    · left; rw [h]; norm_num



def markedProductCylinder {ι Y : Type*} [Fintype ι] [TopologicalSpace Y]
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y) :
    (sphere (0 : ι → ℝ) 1 × Icc (0 : ℝ) 1) ≃ₜ Y :=
  ((Homeomorph.refl _).prodCongr markedIntervalBallCoordinates).trans
    ((Homeomorph.Set.prod _ _).symm.trans P)

theorem markedProductCylinder_apply {ι Y : Type*} [Fintype ι] [TopologicalSpace Y]
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y)
    (z : sphere (0 : ι → ℝ) 1 × Icc (0 : ℝ) 1) :
    markedProductCylinder P z = P ⟨((z.1 : ι → ℝ), fun _ => 3 * (z.2 : ℝ) - 3 / 2),
      z.1.property, (markedIntervalBallCoordinates z.2).property⟩ := rfl




theorem marked_product_lower_rim_data
    {ι Y B : Type*} [Fintype ι] [TopologicalSpace Y] [TopologicalSpace B]
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y)
    (e : sphere (0 : ι → ℝ) 1 ≃ₜ B) (i : C(B, Y))
    (hmark : ∀ x : sphere (0 : ι → ℝ) 1,
      P ⟨((x : ι → ℝ), fun _ => -(3 / 2 : ℝ)), x.property, by
        rw [mem_closedBall_zero_iff, pi_norm_const, Real.norm_eq_abs]
        norm_num⟩ = i (e x)) (b : B) :
    Function.Surjective (FundamentalGroup.map i b) ∧
      ∃ c : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) Y,
        c.source = univ ∧ ∀ a, c (collarBase a) = i a := by
  have hbase (x : sphere (0 : ι → ℝ) 1) :
      markedProductCylinder P (x, ⟨0, by norm_num⟩) = i (e x) := by
    rw [markedProductCylinder_apply]
    convert hmark x using 1
    simp
  exact ⟨marked_cylinder_rim_generates (markedProductCylinder P) e i hbase b,
    exists_marked_cylinder_rim_collar (markedProductCylinder P) e i hbase b⟩

end PoincareConjecture.M76
