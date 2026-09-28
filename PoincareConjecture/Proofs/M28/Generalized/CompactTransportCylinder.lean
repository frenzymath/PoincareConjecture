import PoincareConjecture.Proofs.M28.Generalized.BoxSpacetimeTransport
import PoincareConjecture.Proofs.M28.Generalized.CompactBoxLifetime
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M28

variable (F : GeneralizedRicciFlowData.{u}) {ι : Type v} (b : ι → F.box_index)
    (t : ℝ) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (J : Set ℝ) (hJF : J ⊆ F.interval)
    (hJ : ∀ s ∈ J, ∀ i, s ∈ (F.box (b i)).interval)
    (htF : t ∈ F.interval)
    (hJopen : ∃ V : Set ℝ, IsOpen V ∧ J = F.interval ∩ V)

noncomputable def boxTransportCylinder :
    GeneralizedFlowCylinder F (F.slice t) t 1 {s : ℝ | t + s ∈ J}
      (range (boxEvaluation F b t ht)) := by
  let I : Set ℝ := {s | t + s ∈ J}
  let U := range (boxEvaluation F b t ht)
  have hphysical (s : ℝ) (hs : s ∈ I) : t + s / 1 ∈ J := by
    simpa only [div_one] using (show t + s ∈ J from hs)
  let forward := fun s (hs : s ∈ I) =>
    boxTransport F b t (t + s / 1) ht (hJ _ (hphysical s hs)) (hJF (hphysical s hs))
  let inverse := fun s (hs : s ∈ I) =>
    boxTransport F b (t + s / 1) t (hJ _ (hphysical s hs)) ht htF
  have himage (s : ℝ) (hs : s ∈ I) : forward s hs '' U ⊆
      range (boxEvaluation F b (t + s / 1) (hJ _ (hphysical s hs))) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (boxTransportDiffeomorph F b t (t + s / 1) ht
      (hJ _ (hphysical s hs)) htF (hJF (hphysical s hs))).map_source hx
  refine {
    scale_pos := zero_lt_one
    forward := forward
    inverse := inverse
    forward_smooth := fun s hs => boxTransport_contMDiffOn F b t (t + s / 1)
      ht (hJ _ (hphysical s hs)) (hJF (hphysical s hs))
    inverse_smooth := fun s hs => (boxTransport_contMDiffOn F b (t + s / 1) t
      (hJ _ (hphysical s hs)) ht htF).mono (himage s hs)
    left_inverse := fun s hs => boxTransport_leftInverse F b t (t + s / 1)
      ht (hJ _ (hphysical s hs)) htF (hJF (hphysical s hs))
    right_inverse := fun s hs y hy => boxTransport_leftInverse F b (t + s / 1) t
      (hJ _ (hphysical s hs)) ht (hJF (hphysical s hs)) htF (himage s hs hy)
    embedding := ?_
    vertical_compatibility := ?_ }
  · have hclock : Topology.IsEmbedding
        (fun s : I => (⟨t + s.val / 1, hphysical s.val s.property⟩ : J)) := by
      convert ((Homeomorph.addLeft t).sets (s := I) (t := J) rfl).isEmbedding using 1
      funext s
      apply Subtype.ext
      simp
    exact (isOpenEmbedding_boxSpacetimeTransport F b t ht J hJF hJ htF hJopen).isEmbedding.comp
      (hclock.prodMap .id)
  · intro s _ x hx
    obtain ⟨⟨i, y⟩, rfl⟩ := hx
    refine ⟨b i, y, 1, zero_lt_one, fun s' hs' _ => ?_⟩
    exact ⟨hJ _ (hphysical s' hs') i,
      boxTransport_apply F b t (t + s' / 1) ht
        (hJ _ (hphysical s' hs')) (hJF (hphysical s' hs')) i y⟩

theorem boxTransportCylinder_zero (htJ : t ∈ J)
    (x : (F.slice t).carrier) (hx : x ∈ range (boxEvaluation F b t ht)) :
    (boxTransportCylinder F b t ht J hJF hJ htF hJopen).pointMap
      0 (by simpa only [mem_ofPred, add_zero] using htJ) x = ⟨t, x⟩ := by
  obtain ⟨⟨i, y⟩, rfl⟩ := hx
  simp only [GeneralizedFlowCylinder.pointMap, boxTransportCylinder,
    boxEvaluation, boxTransport_apply]
  have h0t : t + 0 / 1 ∈ (F.box (b i)).interval := by simpa using ht i
  have heq : (⟨t + 0 / 1, h0t⟩ : (F.box (b i)).interval) = ⟨t, ht i⟩ :=
    Subtype.ext (by simp)
  exact congrArg (fun s : (F.box (b i)).interval =>
    (⟨s.val, (F.box (b i)).forward s.val s.property y⟩ : F.point)) heq

theorem exists_compact_transport_cylinder
    (F : GeneralizedRicciFlowData.{u}) (t : ℝ) (htF : t ∈ F.interval)
    (K : Set (F.slice t).carrier) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set (F.slice t).carrier,
      IsOpen U ∧ K ⊆ U ∧
      ∃ e : GeneralizedFlowCylinder F (F.slice t) t 1
        {s : ℝ | t + s ∈ F.interval ∩ Ioo (t - δ) (t + δ)} U,
        ∀ (h0 : 0 ∈ {s : ℝ | t + s ∈ F.interval ∩ Ioo (t - δ) (t + δ)})
          (x : (F.slice t).carrier), x ∈ U → e.pointMap 0 h0 x = ⟨t, x⟩ := by
  obtain ⟨B, hB, δ, hδ, hlife⟩ := F.exists_common_box_lifetime t K hK
  let b : B → F.box_index := fun i => i.val.val
  have ht (i : B) : t ∈ (F.box (b i)).interval := i.val.property
  let J := F.interval ∩ Ioo (t - δ) (t + δ)
  have hJF : J ⊆ F.interval := inter_subset_left
  have hJ (s : ℝ) (hs : s ∈ J) (i : B) : s ∈ (F.box (b i)).interval := by
    apply hlife s hs.1 _ i.val i.property
    exact abs_lt.mpr ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
  have hJopen : ∃ V : Set ℝ, IsOpen V ∧ J = F.interval ∩ V :=
    ⟨Ioo (t - δ) (t + δ), isOpen_Ioo, rfl⟩
  have htJ : t ∈ J := ⟨htF, by constructor <;> linarith⟩
  refine ⟨δ, hδ, range (boxEvaluation F b t ht),
    isOpen_range_boxEvaluation F b t ht, ?_,
    boxTransportCylinder F b t ht J hJF hJ htF hJopen, ?_⟩
  · intro x hx
    obtain ⟨i, hi, y, hy⟩ := mem_iUnion₂.mp (hB hx)
    exact ⟨⟨⟨i, hi⟩, y⟩, hy⟩
  · intro h0 x hx
    exact boxTransportCylinder_zero F b t ht J hJF hJ htF hJopen htJ x hx

end PoincareConjecture.M28
