import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (f : E → F) {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
variable (hd : ∀ x ∈ U, ∃ A : E ≃L[ℝ] F, HasFDerivAt f (A : E →L[ℝ] F) x)

include hU hf hd

theorem isOpen_image_of_invertible_derivative {T : Set E} (hT : IsOpen T) (hTU : T ⊆ U) :
    IsOpen (f '' T) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨A, hA⟩ := hd x (hTU hx)
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds (hTU hx))
  let e := hfx.toOpenPartialHomeomorph f hA (by simp)
  have hxe : x ∈ e.source := hfx.mem_toOpenPartialHomeomorph_source hA (by simp)
  have ho : IsOpen (f '' (e.source ∩ T)) :=
    e.isOpen_image_of_subset_source (e.open_source.inter hT) inter_subset_left
  exact mem_of_superset (ho.mem_nhds ⟨x, ⟨hxe, hx⟩, rfl⟩)
    (image_mono inter_subset_right)

theorem isOpenMap_restrict_of_invertible_derivative : IsOpenMap (U.domRestrict f) := by
  intro T hT
  have hopen : IsOpen (Subtype.val '' T : Set E) :=
    hU.isOpenEmbedding_subtypeVal.isOpenMap T hT
  have hsub : (Subtype.val '' T : Set E) ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.2
  rw [domRestrict_eq, image_comp]
  exact isOpen_image_of_invertible_derivative f hU hf hd hopen hsub

variable (hi : InjOn f U)

noncomputable def smoothOpenChart : OpenPartialHomeomorph E F :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U)
    hf.continuousOn (isOpenMap_restrict_of_invertible_derivative f hU hf hd) hU

@[simp] theorem smoothOpenChart_apply (x : E) : smoothOpenChart f hU hf hd hi x = f x := rfl

@[simp] theorem smoothOpenChart_source : (smoothOpenChart f hU hf hd hi).source = U := rfl

@[simp] theorem smoothOpenChart_target : (smoothOpenChart f hU hf hd hi).target = f '' U := rfl

theorem smoothOpenChart_contDiffOn :
    ContDiffOn ℝ ∞ (smoothOpenChart f hU hf hd hi) U := hf

theorem smoothOpenChart_symm_contDiffOn :
    ContDiffOn ℝ ∞ (smoothOpenChart f hU hf hd hi).symm (f '' U) := by
  let e := smoothOpenChart f hU hf hd hi
  intro y hy
  have hx : e.symm y ∈ U := e.map_target hy
  obtain ⟨A, hA⟩ := hd (e.symm y) hx
  exact (e.contDiffAt_symm hy hA (hf.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt

end PoincareConjecture.M25.Topology3D
