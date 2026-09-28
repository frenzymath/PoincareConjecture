import PoincareConjecture.Proofs.M76.Mathlib.ClosedPartitionHeightSigns

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

theorem mem_both_height_closures_of_closed_band_cover
    {S R Z : Set E} {R' : Set F} (H : R ≃ₜ R') (A : E → ℝ) (B : F → ℝ)
    (hA : Continuous A) (hheight : ∀ y : R, B (H y) = A y)
    {a b : ℝ} (hZ : IsClosed Z)
    (hcover : (R ∩ {y | A y ∈ Icc a b}) ∪ Z = S ∩ {y | A y ∈ Icc a b})
    (x : R) (hxZ : (x : E) ∉ Z) (ha : a < A x) (hb : A x < b)
    (hlo : (x : E) ∈ closure (S ∩ {y | A y < A x}))
    (hhi : (x : E) ∈ closure (S ∩ {y | A x < A y})) :
    (H x : F) ∈ closure (R' ∩ {y | B y < B (H x)}) ∧
      (H x : F) ∈ closure (R' ∩ {y | B (H x) < B y}) := by
  let U := {y : E | A y ∈ Ioo a b} ∩ Zᶜ
  have hU : IsOpen U := (isOpen_Ioo.preimage hA).inter hZ.isOpen_compl
  have hxU : (x : E) ∈ U := ⟨⟨ha, hb⟩, hxZ⟩
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
