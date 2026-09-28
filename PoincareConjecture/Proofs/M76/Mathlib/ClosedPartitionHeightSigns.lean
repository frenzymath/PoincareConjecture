import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas










set_option autoImplicit false

open Set

namespace Homeomorph

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]





theorem mem_both_height_closures_of_height_preserving
    {R : Set E} {R' : Set F} (H : R ≃ₜ R') (A : E → ℝ) (B : F → ℝ)
    (hheight : ∀ y : R, B (H y) = A y) (x : R)
    (hlo : (x : E) ∈ closure (R ∩ {y | A y < A x}))
    (hhi : (x : E) ∈ closure (R ∩ {y | A x < A y})) :
    (H x : F) ∈ closure (R' ∩ {y | B y < B (H x)}) ∧
      (H x : F) ∈ closure (R' ∩ {y | B (H x) < B y}) := by
  have hxlo : x ∈ closure ((Subtype.val : R → E) ⁻¹' {y | A y < A x}) := by
    rwa [closure_subtype, Subtype.image_preimage_val]
  have hxhi : x ∈ closure ((Subtype.val : R → E) ⁻¹' {y | A x < A y}) := by
    rwa [closure_subtype, Subtype.image_preimage_val]
  have hcont : Continuous (fun y : R => (H y : F)) :=
    continuous_subtype_val.comp H.continuous
  constructor
  · apply hcont.continuousWithinAt.mem_closure hxlo
    intro y hy
    refine ⟨(H y).property, ?_⟩
    change B (H y) < B (H x)
    rw [hheight y, hheight x]
    exact hy
  · apply hcont.continuousWithinAt.mem_closure hxhi
    intro y hy
    refine ⟨(H y).property, ?_⟩
    change B (H x) < B (H y)
    rw [hheight y, hheight x]
    exact hy





theorem mem_both_height_closures_of_closed_band_partition
    {S R Z : Set E} {R' : Set F} (H : R ≃ₜ R') (A : E → ℝ) (B : F → ℝ)
    (hA : Continuous A) (hheight : ∀ y : R, B (H y) = A y)
    {a b : ℝ} (hZ : IsClosed Z)
    (hcover : (R ∩ {y | A y ∈ Icc a b}) ∪ Z = S ∩ {y | A y ∈ Icc a b})
    (hdisj : Disjoint (R ∩ {y | A y ∈ Icc a b}) Z)
    (x : R) (ha : a < A x) (hb : A x < b)
    (hlo : (x : E) ∈ closure (S ∩ {y | A y < A x}))
    (hhi : (x : E) ∈ closure (S ∩ {y | A x < A y})) :
    (H x : F) ∈ closure (R' ∩ {y | B y < B (H x)}) ∧
      (H x : F) ∈ closure (R' ∩ {y | B (H x) < B y}) := by
  let U := {y : E | A y ∈ Ioo a b} ∩ Zᶜ
  have hU : IsOpen U := (isOpen_Ioo.preimage hA).inter hZ.isOpen_compl
  have hxU : (x : E) ∈ U := ⟨⟨ha, hb⟩,
    fun hxZ => disjoint_left.mp hdisj ⟨x.property, ⟨ha.le, hb.le⟩⟩ hxZ⟩
  have hlocal : S ∩ U ⊆ R := by
    intro y hy
    rcases hcover.symm.subset ⟨hy.1, ⟨hy.2.1.1.le, hy.2.1.2.le⟩⟩ with hyR | hyZ
    · exact hyR.1
    · exact (hy.2.2 hyZ).elim
  have hrestrict {V : Set E} (hx : (x : E) ∈ closure (S ∩ V)) :
      (x : E) ∈ closure (R ∩ V) := by
    apply closure_mono _ (hU.inter_closure ⟨hxU, hx⟩)
    intro y hy
    exact ⟨hlocal ⟨hy.2.1, hy.1⟩, hy.2.2⟩
  exact H.mem_both_height_closures_of_height_preserving A B hheight x
    (hrestrict hlo) (hrestrict hhi)

end Homeomorph
