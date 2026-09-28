import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionRadialCoordinates

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M74

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

def collarReflect (p : RoundCylinderSpace) : RoundCylinderSpace := (p.1, -p.2)

theorem collarReflect_involutive : Function.Involutive collarReflect := by
  intro p
  simp [collarReflect]

theorem collarReflect_mem_band (p : RoundCylinderSpace) (a : ℝ) :
    collarReflect p ∈ univ ×ˢ Ioo (-a) a ↔ p ∈ univ ×ˢ Ioo (-a) a := by
  simp only [mem_prod, mem_univ, true_and, mem_Ioo, collarReflect]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem collarReflect_contMDiff : ContMDiff ICollar ICollar ∞ collarReflect :=
  contMDiff_fst.prodMk contMDiff_snd.neg

structure CollarEndChartData (Y : GeneralizedSliceCarrier.{u}) where
  first : OpenPartialHomeomorph Y.carrier StandardCapSpace
  second : OpenPartialHomeomorph Y.carrier StandardCapSpace
  first_target : first.target = univ
  second_target : second.target = univ
  disjoint : Disjoint first.source second.source
  first_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ first first.source
  second_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ second second.source
  first_inverse_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ first.symm
  second_inverse_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ second.symm
  width : ℝ
  width_pos : 0 < width
  neck : OpenPartialHomeomorph RoundCylinderSpace Y.carrier
  neck_source : neck.source = univ ×ˢ Ioo (-width) width
  neck_smooth : ContMDiffOn ICollar (𝓡 3) ∞ neck neck.source
  neck_inverse_smooth : ContMDiffOn (𝓡 3) ICollar ∞ neck.symm neck.target
  negative_mem : ∀ q s, s ∈ Ioo (-width) 0 → neck (q, s) ∈ first.source
  positive_mem : ∀ q s, s ∈ Ioo 0 width → neck (q, s) ∈ second.source
  negative_eq : ∀ q s, s ∈ Ioo (-width) 0 → first (neck (q, s)) = (-1 / s) • q.1
  positive_eq : ∀ q s, s ∈ Ioo 0 width → second (neck (q, s)) = (1 / s) • q.1
  central_disjoint : ∀ q, neck (q, 0) ∉ first.source ∪ second.source
  cover : first.source ∪ second.source ∪ neck '' (univ ×ˢ ({0} : Set ℝ)) = univ

namespace CollarEndChartData

variable {Y : GeneralizedSliceCarrier.{u}} (D : CollarEndChartData Y)

theorem central_mem_source (q : UnitTwoSphere) : (q, 0) ∈ D.neck.source := by
  rw [D.neck_source]
  exact ⟨mem_univ _, neg_neg_of_pos D.width_pos, D.width_pos⟩

theorem cover_cases (x : Y.carrier) :
    x ∈ D.first.source ∨ x ∈ D.second.source ∨ ∃ q, D.neck (q, 0) = x := by
  have hx : x ∈ D.first.source ∪ D.second.source ∪
      D.neck '' (univ ×ˢ ({0} : Set ℝ)) := D.cover.symm ▸ mem_univ x
  rcases hx with (hx | hx) | ⟨⟨q, s⟩, hs, hq⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · have hs0 : s = 0 := hs.2
    subst s
    exact Or.inr (Or.inr ⟨q, hq⟩)

theorem mem_first_target (z : StandardCapSpace) : z ∈ D.first.target := by
  rw [D.first_target]
  trivial

theorem mem_second_target (z : StandardCapSpace) : z ∈ D.second.target := by
  rw [D.second_target]
  trivial

theorem centers_ne : D.first.symm 0 ≠ D.second.symm 0 := by
  intro h
  have h₁ := D.first.map_target (D.mem_first_target 0)
  have h₂ := D.second.map_target (D.mem_second_target 0)
  rw [h] at h₁
  exact disjoint_left.mp D.disjoint h₁ h₂

noncomputable def reflectedNeck : OpenPartialHomeomorph RoundCylinderSpace Y.carrier where
  toFun p := D.neck (collarReflect p)
  invFun x := collarReflect (D.neck.symm x)
  source := univ ×ˢ Ioo (-D.width) D.width
  target := D.neck.target
  map_source' p hp := D.neck.map_source (by
    rw [D.neck_source]
    exact (collarReflect_mem_band p D.width).mpr hp)
  map_target' x hx := by
    have h := D.neck.map_target hx
    rw [D.neck_source] at h
    exact (collarReflect_mem_band (D.neck.symm x) D.width).mpr h
  left_inv' p hp := by
    rw [D.neck.left_inv (by
      rw [D.neck_source]
      exact (collarReflect_mem_band p D.width).mpr hp)]
    exact collarReflect_involutive p
  right_inv' x hx := by
    rw [collarReflect_involutive]
    exact D.neck.right_inv hx
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := D.neck.open_target
  continuousOn_toFun := D.neck.continuousOn.comp
    collarReflect_contMDiff.continuous.continuousOn (by
      intro p hp
      rw [D.neck_source]
      exact (collarReflect_mem_band p D.width).mpr hp)
  continuousOn_invFun :=
    collarReflect_contMDiff.continuous.comp_continuousOn D.neck.continuousOn_symm

@[simp] theorem reflectedNeck_apply (p : RoundCylinderSpace) :
    D.reflectedNeck p = D.neck (collarReflect p) := rfl

private theorem reflectedNeck_central :
    D.reflectedNeck '' (univ ×ˢ ({0} : Set ℝ)) =
      D.neck '' (univ ×ˢ ({0} : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨⟨q, s⟩, hs, hx⟩
    have hs0 : s = 0 := hs.2
    subst s
    exact ⟨(q, 0), ⟨mem_univ _, mem_singleton 0⟩,
      by simpa only [reflectedNeck_apply, collarReflect, neg_zero] using hx⟩
  · rintro ⟨⟨q, s⟩, hs, hx⟩
    have hs0 : s = 0 := hs.2
    subst s
    exact ⟨(q, 0), ⟨mem_univ _, mem_singleton 0⟩,
      by simpa only [reflectedNeck_apply, collarReflect, neg_zero] using hx⟩

noncomputable def swap : CollarEndChartData Y where
  first := D.second
  second := D.first
  first_target := D.second_target
  second_target := D.first_target
  disjoint := D.disjoint.symm
  first_smooth := D.second_smooth
  second_smooth := D.first_smooth
  first_inverse_smooth := D.second_inverse_smooth
  second_inverse_smooth := D.first_inverse_smooth
  width := D.width
  width_pos := D.width_pos
  neck := D.reflectedNeck
  neck_source := rfl
  neck_smooth := D.neck_smooth.comp collarReflect_contMDiff.contMDiffOn (by
    intro p hp
    rw [D.neck_source]
    exact (collarReflect_mem_band p D.width).mpr hp)
  neck_inverse_smooth :=
    collarReflect_contMDiff.comp_contMDiffOn D.neck_inverse_smooth
  negative_mem q s hs := D.positive_mem q (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  positive_mem q s hs := D.negative_mem q (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  negative_eq q s hs := by
    change D.second (D.neck (q, -s)) = (-1 / s) • q.1
    rw [D.positive_eq q (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]
    congr 1
    simp [div_eq_mul_inv]
  positive_eq q s hs := by
    change D.first (D.neck (q, -s)) = (1 / s) • q.1
    rw [D.negative_eq q (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩]
    congr 1
    simp
  central_disjoint q := by
    change D.neck (q, -0) ∉ D.second.source ∪ D.first.source
    simpa only [neg_zero, union_comm] using D.central_disjoint q
  cover := by
    rw [D.reflectedNeck_central, union_comm D.second.source D.first.source, D.cover]

end CollarEndChartData

end PoincareConjecture.M74
