import PoincareConjecture.Proofs.M54.ConnectedSum.Collars

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SmoothConnectedSumData

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {A B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)

noncomputable def collarChart : OpenPartialHomeomorph RoundCylinderSpace C.carrier where
  toFun := S.collar
  invFun := S.collar_inverse
  source := univ ×ˢ Ioo (-1 : ℝ) 1
  target := S.collar '' (univ ×ˢ Ioo (-1 : ℝ) 1)
  map_source' _ hp := mem_image_of_mem _ hp
  map_target' x hx := by
    obtain ⟨p, hp, rfl⟩ := hx
    simpa only [S.collar_left_inverse hp] using hp
  left_inv' _ hp := S.collar_left_inverse hp
  right_inv' _ hx := S.collar_right_inverse hx
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := S.collar_open
  continuousOn_toFun := S.collar_smooth.continuousOn
  continuousOn_invFun := S.collar_inverse_smooth.continuousOn

theorem collarWidth_subset {a : ℝ} (ha : a ≤ 1) :
    (univ ×ˢ Ioo (-a) a : Set RoundCylinderSpace) ⊆ univ ×ˢ Ioo (-1 : ℝ) 1 := by
  intro p hp
  exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩

noncomputable def collarChartOfWidth (a : ℝ) (ha : a ≤ 1) :
    OpenPartialHomeomorph RoundCylinderSpace C.carrier where
  toFun := S.collar
  invFun := S.collar_inverse
  source := univ ×ˢ Ioo (-a) a
  target := S.collar '' (univ ×ˢ Ioo (-a) a)
  map_source' _ hp := mem_image_of_mem _ hp
  map_target' x hx := by
    obtain ⟨p, hp, rfl⟩ := hx
    simpa only [S.collar_left_inverse (collarWidth_subset ha hp)] using hp
  left_inv' _ hp := S.collar_left_inverse (collarWidth_subset ha hp)
  right_inv' _ hx := S.collar_right_inverse (image_mono (collarWidth_subset ha) hx)
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := S.collarChart.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) (collarWidth_subset ha)
  continuousOn_toFun := S.collar_smooth.continuousOn.mono (collarWidth_subset ha)
  continuousOn_invFun :=
    S.collar_inverse_smooth.continuousOn.mono (image_mono (collarWidth_subset ha))

@[simp] theorem collarChartOfWidth_source (a : ℝ) (ha : a ≤ 1) :
    (S.collarChartOfWidth a ha).source = univ ×ˢ Ioo (-a) a := rfl

@[simp] theorem collarChartOfWidth_apply (a : ℝ) (ha : a ≤ 1) (p : RoundCylinderSpace) :
    S.collarChartOfWidth a ha p = S.collar p := rfl

@[simp] theorem collarChartOfWidth_symm_apply (a : ℝ) (ha : a ≤ 1) (x : C.carrier) :
    (S.collarChartOfWidth a ha).symm x = S.collar_inverse x := rfl

theorem collarChartOfWidth_contMDiffOn (a : ℝ) (ha : a ≤ 1) :
    ContMDiffOn ICollar (𝓡 3) ∞ (S.collarChartOfWidth a ha)
      (S.collarChartOfWidth a ha).source :=
  S.collar_smooth.mono (collarWidth_subset ha)

theorem collarChartOfWidth_symm_contMDiffOn (a : ℝ) (ha : a ≤ 1) :
    ContMDiffOn (𝓡 3) ICollar ∞ (S.collarChartOfWidth a ha).symm
      (S.collarChartOfWidth a ha).target :=
  S.collar_inverse_smooth.mono (image_mono (collarWidth_subset ha))

end PoincareConjecture.SmoothConnectedSumData
