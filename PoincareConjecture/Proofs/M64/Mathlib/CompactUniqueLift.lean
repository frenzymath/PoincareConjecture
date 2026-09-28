import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Hausdorff









noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture





theorem m64_exists_continuous_lift_of_compact_unique_fibers
    {X Y Z : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z]
    {K : Set X} (hK : IsCompact K) {f : X → Y} (hf : ContinuousOn f K)
    {J : Set Z} (hJ : IsCompact J) {g : Z → Y} (hg : ContinuousOn g J)
    (hunique : ∀ z ∈ J, ∃! x, x ∈ K ∧ f x = g z) :
    ∃ u : J → X, Continuous u ∧ ∀ z : J, u z ∈ K ∧ f (u z) = g z := by
  classical
  let C : Set X := K ∩ f ⁻¹' (g '' J)
  have hC : IsCompact C := hK.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed hK.isClosed
      (hJ.image_of_continuousOn hg).isClosed) inter_subset_left
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let F : C → Y := fun x => f x
  have hF : Continuous F := (hf.mono inter_subset_left).domRestrict
  have hFi : Function.Injective F := by
    intro x y hxy
    obtain ⟨z, hz, hzx⟩ := x.property.2
    apply Subtype.ext
    exact (hunique z hz).unique ⟨x.property.1, hzx.symm⟩
      ⟨y.property.1, hxy.symm.trans hzx.symm⟩
  choose u hu using (fun z : J => (hunique z z.property).exists)
  let v : J → C := fun z => ⟨u z, (hu z).1, ⟨z, z.property, (hu z).2.symm⟩⟩
  have hv : Continuous v := (hF.isClosedEmbedding hFi).isEmbedding.continuous_iff.mpr
    (hg.domRestrict.congr (fun z => (hu z).2.symm))
  exact ⟨u, continuous_subtype_val.comp hv, hu⟩

end PoincareConjecture
