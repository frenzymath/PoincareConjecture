import PoincareConjecture.Proofs.M28.Generalized.BoxPathLength
import PoincareConjecture.Proofs.M28.Generalized.CompactTransportCylinder
import PoincareConjecture.Proofs.M28.Generalized.ScalarContinuity












set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28





theorem exists_compact_path_transport
    (F : GeneralizedRicciFlowData.{u}) (P : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (htF : t ∈ F.interval)
    (γ : ℝ → (F.slice t).carrier) (hγ : ContMDiff 𝓘(ℝ) (𝓡 3) 1 γ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ Γ : ∀ s : ↥(F.interval ∩ Ioo (t - δ) (t + δ)), ℝ → (F.slice s.val).carrier,
        (∀ s, ContMDiffOn 𝓘(ℝ) (𝓡 3) 1 (Γ s) (Icc 0 1)) ∧
        (∀ ht : t ∈ F.interval ∩ Ioo (t - δ) (t + δ),
          ∀ v ∈ Icc (0 : ℝ) 1, Γ ⟨t, ht⟩ v = γ v) ∧
        Continuous (fun z : ↥(F.interval ∩ Ioo (t - δ) (t + δ)) × unitInterval =>
          F.scalar ⟨z.1.val, Γ z.1 z.2.val⟩) ∧
        Continuous (fun s : ↥(F.interval ∩ Ioo (t - δ) (t + δ)) =>
          (F.metric s.val).pathELength (Γ s) 0 1) := by
  obtain ⟨B, hB, δ, hδ, hlife⟩ := F.exists_common_box_lifetime t
    (γ '' Icc 0 1) (isCompact_Icc.image hγ.continuous)
  let b : B → F.box_index := fun i => i.val.val
  have ht (i : B) : t ∈ (F.box (b i)).interval := i.val.property
  let J := F.interval ∩ Ioo (t - δ) (t + δ)
  have hJF : J ⊆ F.interval := inter_subset_left
  have hJ (s : ℝ) (hs : s ∈ J) (i : B) : s ∈ (F.box (b i)).interval := by
    apply hlife s hs.1 _ i.val i.property
    exact abs_lt.mpr ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
  let U := range (boxEvaluation F b t ht)
  have himage : MapsTo γ (Icc 0 1) U := by
    intro v hv
    obtain ⟨i, hi, y, hy⟩ := mem_iUnion₂.mp (hB (mem_image_of_mem γ hv))
    exact ⟨⟨⟨i, hi⟩, y⟩, hy⟩
  let Γ : ∀ s : J, ℝ → (F.slice s.val).carrier := fun s =>
    boxTransport F b t s.val ht (hJ _ s.property) (hJF s.property) ∘ γ
  refine ⟨δ, hδ, Γ, ?_, ?_, ?_, ?_⟩
  · intro s
    exact ((boxTransport_contMDiffOn F b t s.val ht (hJ _ s.property)
      (hJF s.property)).of_le (by norm_num)).comp hγ.contMDiffOn himage
  · intro htJ v hv
    obtain ⟨⟨i, y⟩, hy⟩ := himage hv
    change boxTransport F b t t ht (hJ t htJ) (hJF htJ) (γ v) = γ v
    rw [← hy]
    exact boxTransport_apply F b t t ht (hJ t htJ) (hJF htJ) i y
  · have hJopen : ∃ V : Set ℝ, IsOpen V ∧ J = F.interval ∩ V :=
      ⟨Ioo (t - δ) (t + δ), isOpen_Ioo, rfl⟩
    have hsp := (isOpenEmbedding_boxSpacetimeTransport F b t ht J hJF hJ htF hJopen).continuous
    have hpath : Continuous (fun z : J × unitInterval =>
        (z.1, (⟨γ z.2.val, himage z.2.property⟩ : U))) :=
      continuous_fst.prodMk
        ((hγ.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
    exact (F.continuous_scalar_m28 P).comp (hsp.comp hpath)
  · exact continuous_boxTransport_pathELength F b t ht J hJF hJ γ hγ himage

end PoincareConjecture.M28
