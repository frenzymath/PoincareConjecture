import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Set

namespace Set.InjOn

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]



theorem isOpen_smaller_band_image {A : Set E} (hA : IsCompact A)
    {F : E × ℝ → X} (hFi : InjOn F (A ×ˢ Icc (-1 : ℝ) 1))
    (hF : ContinuousOn F (A ×ˢ Icc (-1 : ℝ) 1)) {B : Set X}
    (hopen : IsOpen ((Subtype.val : B → X) ⁻¹'
      (F '' (A ×ˢ Ioo (-1 : ℝ) 1)))) {a : ℝ} (ha1 : a ≤ 1) :
    IsOpen ((Subtype.val : B → X) ⁻¹' (F '' (A ×ˢ Ioo (-a) a))) := by
  let Z := F '' (A ×ˢ (Icc (-1 : ℝ) 1 \ Ioo (-a) a))
  have hZ : IsCompact Z :=
    (hA.prod (isCompact_Icc.diff isOpen_Ioo)).image_of_continuousOn
      (hF.mono (fun _ hz => ⟨hz.1, hz.2.1⟩))
  have hsmall : A ×ˢ Ioo (-a) a ⊆ A ×ˢ Ioo (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have heq : F '' (A ×ˢ Ioo (-a) a) =
      (F '' (A ×ˢ Ioo (-1 : ℝ) 1)) \ Z := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨⟨z, hsmall hz, rfl⟩, ?_⟩
      rintro ⟨w, hw, hwz⟩
      have he := hFi ⟨hw.1, hw.2.1⟩
        ⟨hz.1, Ioo_subset_Icc_self (hsmall hz).2⟩ hwz
      apply hw.2.2
      rw [he]
      exact hz.2
    · rintro _ ⟨⟨z, hz, rfl⟩, hnot⟩
      refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
      by_contra ht
      exact hnot ⟨z, ⟨hz.1, Ioo_subset_Icc_self hz.2, ht⟩, rfl⟩
  rw [heq, preimage_sdiff]
  exact hopen.sdiff (hZ.isClosed.preimage continuous_subtype_val)

end Set.InjOn
