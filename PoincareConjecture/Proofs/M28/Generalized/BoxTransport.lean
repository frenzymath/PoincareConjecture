import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M28

variable (F : GeneralizedRicciFlowData.{u}) {ι : Type v} (b : ι → F.box_index)

def boxEvaluation (t : ℝ) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (q : Σ i, (F.box (b i)).carrier.carrier) : (F.slice t).carrier :=
  (F.box (b q.1)).forward t (ht q.1) q.2

theorem range_boxEvaluation (t : ℝ) (ht : ∀ i, t ∈ (F.box (b i)).interval) :
    range (boxEvaluation F b t ht) = ⋃ i, range ((F.box (b i)).forward t (ht i)) := by
  ext x
  constructor
  · rintro ⟨⟨i, y⟩, hy⟩
    exact mem_iUnion.mpr ⟨i, y, hy⟩
  · intro hx
    obtain ⟨i, y, hy⟩ := mem_iUnion.mp hx
    exact ⟨⟨i, y⟩, hy⟩

theorem isOpen_range_boxEvaluation (t : ℝ) (ht : ∀ i, t ∈ (F.box (b i)).interval) :
    IsOpen (range (boxEvaluation F b t ht)) := by
  rw [range_boxEvaluation]
  exact isOpen_iUnion fun i => ((F.box (b i)).forward_openEmbedding t (ht i)).isOpen_range

noncomputable def boxTransport (s t : ℝ)
    (hs : ∀ i, s ∈ (F.box (b i)).interval) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (htF : t ∈ F.interval) : (F.slice s).carrier → (F.slice t).carrier :=
  Function.extend (boxEvaluation F b s hs) (boxEvaluation F b t ht)
    (fun _ => Classical.choice ((F.slice_nonempty_iff t).mpr htF))

theorem boxTransport_apply (s t : ℝ)
    (hs : ∀ i, s ∈ (F.box (b i)).interval) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (htF : t ∈ F.interval) (i : ι) (x : (F.box (b i)).carrier.carrier) :
    boxTransport F b s t hs ht htF ((F.box (b i)).forward s (hs i) x) =
      (F.box (b i)).forward t (ht i) x := by
  have hf : (boxEvaluation F b t ht).FactorsThrough (boxEvaluation F b s hs) := by
    intro a c h
    exact F.vertical_compatibility (b a.1) (b c.1) s (hs a.1) (hs c.1)
      a.2 c.2 h t (ht a.1) (ht c.1)
  exact hf.extend_apply _ ⟨i, x⟩

theorem boxTransport_leftInverse (s t : ℝ)
    (hs : ∀ i, s ∈ (F.box (b i)).interval) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (hsF : s ∈ F.interval) (htF : t ∈ F.interval) :
    LeftInvOn (boxTransport F b t s ht hs hsF) (boxTransport F b s t hs ht htF)
      (range (boxEvaluation F b s hs)) := by
  rintro _ ⟨⟨i, x⟩, rfl⟩
  change boxTransport F b t s ht hs hsF
    (boxTransport F b s t hs ht htF ((F.box (b i)).forward s (hs i) x)) = _
  rw [boxTransport_apply, boxTransport_apply]
  rfl

theorem boxTransport_contMDiffOn (s t : ℝ)
    (hs : ∀ i, s ∈ (F.box (b i)).interval) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (htF : t ∈ F.interval) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (boxTransport F b s t hs ht htF)
      (range (boxEvaluation F b s hs)) := by
  rintro _ ⟨⟨i, x⟩, rfl⟩
  have hopen := ((F.box (b i)).forward_openEmbedding s (hs i)).isOpen_range
  have hinv := ((F.box (b i)).inverse_smooth s (hs i)).contMDiffAt
    (hopen.mem_nhds ⟨x, rfl⟩)
  have hcomp := ((F.box (b i)).forward_smooth t (ht i) _).comp _ hinv
  apply (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hopen.mem_nhds ⟨x, rfl⟩] with y hy
  obtain ⟨z, rfl⟩ := hy
  rw [boxTransport_apply, Function.comp_apply, (F.box (b i)).left_inverse s (hs i) z]

noncomputable def boxTransportDiffeomorph (s t : ℝ)
    (hs : ∀ i, s ∈ (F.box (b i)).interval) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (hsF : s ∈ F.interval) (htF : t ∈ F.interval) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (F.slice s).carrier (F.slice t).carrier ∞ where
  toFun := boxTransport F b s t hs ht htF
  invFun := boxTransport F b t s ht hs hsF
  source := range (boxEvaluation F b s hs)
  target := range (boxEvaluation F b t ht)
  map_source' := by
    rintro _ ⟨⟨i, x⟩, rfl⟩
    exact ⟨⟨i, x⟩, (boxTransport_apply F b s t hs ht htF i x).symm⟩
  map_target' := by
    rintro _ ⟨⟨i, x⟩, rfl⟩
    exact ⟨⟨i, x⟩, (boxTransport_apply F b t s ht hs hsF i x).symm⟩
  left_inv' := boxTransport_leftInverse F b s t hs ht hsF htF
  right_inv' := boxTransport_leftInverse F b t s ht hs htF hsF
  open_source := isOpen_range_boxEvaluation F b s hs
  open_target := isOpen_range_boxEvaluation F b t ht
  contMDiffOn_toFun := boxTransport_contMDiffOn F b s t hs ht htF
  contMDiffOn_invFun := boxTransport_contMDiffOn F b t s ht hs hsF

end PoincareConjecture.M28
