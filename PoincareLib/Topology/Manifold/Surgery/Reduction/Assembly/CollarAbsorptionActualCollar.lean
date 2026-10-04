import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Collars

/-!
# The supplied connected-sum collar as a partial chart

The inverse, smoothness, and open image are all fields of the frozen
connected-sum data. Restricting to a smaller open band gives the collar
used to assemble the canonical ends in MT Corollary 15.4(2), pp. 358-359.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.SmoothConnectedSumData

local notation "ICollar" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {A B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)

/-- The full supplied smooth collar, with its exact source and image
(MT Corollary 15.4(2), pp. 358-359). -/
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

/-- The symmetric smaller collar band lies in the frozen full band
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarWidth_subset {a : ℝ} (ha : a ≤ 1) :
    (univ ×ˢ Ioo (-a) a : Set RoundCylinderSpace) ⊆ univ ×ˢ Ioo (-1 : ℝ) 1 := by
  intro p hp
  exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩

/-- The actual collar restricted to the width where both end formulas
hold (MT Corollary 15.4(2), pp. 358-359). -/
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

/-- The smaller collar has exactly the chosen open band as source
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarChartOfWidth_source (a : ℝ) (ha : a ≤ 1) :
    (S.collarChartOfWidth a ha).source = univ ×ˢ Ioo (-a) a := rfl

/-- Restriction retains the original collar map
(MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarChartOfWidth_apply (a : ℝ) (ha : a ≤ 1) (p : RoundCylinderSpace) :
    S.collarChartOfWidth a ha p = S.collar p := rfl

/-- Restriction also retains the original inverse on its controlled
image (MT Corollary 15.4(2), pp. 358-359). -/
@[simp] theorem collarChartOfWidth_symm_apply (a : ℝ) (ha : a ≤ 1) (x : C.carrier) :
    (S.collarChartOfWidth a ha).symm x = S.collar_inverse x := rfl

/-- The smaller collar's forward map has the supplied smoothness
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarChartOfWidth_contMDiffOn (a : ℝ) (ha : a ≤ 1) :
    ContMDiffOn ICollar (𝓡 3) ∞ (S.collarChartOfWidth a ha)
      (S.collarChartOfWidth a ha).source :=
  S.collar_smooth.mono (collarWidth_subset ha)

/-- The inverse has supplied smoothness on the exact smaller image
(MT Corollary 15.4(2), pp. 358-359). -/
theorem collarChartOfWidth_symm_contMDiffOn (a : ℝ) (ha : a ≤ 1) :
    ContMDiffOn (𝓡 3) ICollar ∞ (S.collarChartOfWidth a ha).symm
      (S.collarChartOfWidth a ha).target :=
  S.collar_inverse_smooth.mono (image_mono (collarWidth_subset ha))

end PoincareMT.SmoothConnectedSumData
