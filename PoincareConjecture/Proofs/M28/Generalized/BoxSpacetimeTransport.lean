import PoincareConjecture.Proofs.M28.Generalized.BoxTransport
import Mathlib.Topology.Maps.OpenQuotient











set_option autoImplicit false

open Set Function Filter
open scoped Topology

universe u v

namespace PoincareConjecture.M28

variable (F : GeneralizedRicciFlowData.{u}) {ι : Type v} (b : ι → F.box_index)
    (t : ℝ) (ht : ∀ i, t ∈ (F.box (b i)).interval)
    (J : Set ℝ) (hJF : J ⊆ F.interval)
    (hJ : ∀ s ∈ J, ∀ i, s ∈ (F.box (b i)).interval)



noncomputable def boxSpacetimeTransport :
    J × range (boxEvaluation F b t ht) → F.point :=
  fun z => ⟨z.1.val, boxTransport F b t z.1.val ht
    (hJ z.1.val z.1.property) (hJF z.1.property) z.2.val⟩




theorem isOpenEmbedding_boxSpacetimeTransport
    (htF : t ∈ F.interval)
    (hJopen : ∃ V : Set ℝ, IsOpen V ∧ J = F.interval ∩ V) :
    Topology.IsOpenEmbedding (boxSpacetimeTransport F b t ht J hJF hJ) := by
  let U := range (boxEvaluation F b t ht)
  let q : (Σ i, J × (F.box (b i)).carrier.carrier) → J × U := fun z =>
    (z.2.1, ⟨(F.box (b z.1)).forward t (ht z.1) z.2.2, ⟨⟨z.1, z.2.2⟩, rfl⟩⟩)
  have hq_i (i : ι) : Topology.IsOpenEmbedding
      (fun z : J × (F.box (b i)).carrier.carrier => q ⟨i, z⟩) := by
    have hsp : Topology.IsOpenEmbedding (fun x : (F.box (b i)).carrier.carrier =>
        (⟨(F.box (b i)).forward t (ht i) x, ⟨⟨i, x⟩, rfl⟩⟩ : U)) :=
      Topology.IsOpenEmbedding.of_comp _
        (isOpen_range_boxEvaluation F b t ht).isOpenEmbedding_subtypeVal
        ((F.box (b i)).forward_openEmbedding t (ht i))
    exact Topology.IsOpenEmbedding.id.prodMap hsp
  have hq : IsOpenQuotientMap q := by
    refine ⟨?_, continuous_sigma (fun i => (hq_i i).continuous),
      isOpenMap_sigma.mpr (fun i => (hq_i i).isOpenMap)⟩
    rintro ⟨s, x, ⟨⟨i, y⟩, hy⟩⟩
    refine ⟨⟨i, s, y⟩, ?_⟩
    exact Prod.ext rfl (Subtype.ext hy)
  let T := boxSpacetimeTransport F b t ht J hJF hJ
  have hcomp_i (i : ι) : (fun z : J × (F.box (b i)).carrier.carrier => T (q ⟨i, z⟩)) =
      (fun z => (⟨z.1.val, (F.box (b i)).forward z.1.val
        (hJ z.1.val z.1.property i) z.2⟩ : F.point)) := by
    funext z
    exact congrArg (fun x => (⟨z.1.val, x⟩ : F.point))
      (boxTransport_apply F b t z.1.val ht (hJ z.1.val z.1.property)
        (hJF z.1.property) i z.2)
  have hcomp (i : ι) : Topology.IsOpenEmbedding
      (fun z : J × (F.box (b i)).carrier.carrier => T (q ⟨i, z⟩)) := by
    rw [hcomp_i]
    have hinc : Topology.IsOpenEmbedding
        (fun s : J => (⟨s.val, hJ s.val s.property i⟩ : (F.box (b i)).interval)) := by
      apply Topology.IsOpenEmbedding.inclusion (fun s hs => hJ s hs i)
      obtain ⟨V, hV, hJV⟩ := hJopen
      have heq : (Subtype.val : (F.box (b i)).interval → ℝ) ⁻¹' J =
          (Subtype.val : (F.box (b i)).interval → ℝ) ⁻¹' V := by
        ext s
        change s.val ∈ J ↔ s.val ∈ V
        rw [hJV]
        have hsF : s.val ∈ F.interval := by
          obtain ⟨W, _, hW⟩ := (F.box (b i)).relatively_open
          exact ((Set.ext_iff.mp hW s.val).mp s.property).1
        exact and_iff_right hsF
      rw [heq]
      exact hV.preimage continuous_subtype_val
    exact (F.box_openEmbedding (b i)).comp (hinc.prodMap .id)
  have hT : Continuous T := hq.continuous_comp_iff.mp
    (continuous_sigma fun i => (hcomp i).continuous)
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hT ?_
    (hq.isOpenMap_iff.mpr (isOpenMap_sigma.mpr fun i => (hcomp i).isOpenMap))
  rintro ⟨s, x⟩ ⟨s', y⟩ hxy
  have hs : s = s' := Subtype.ext (congrArg Sigma.fst hxy)
  subst s'
  have hval : boxTransport F b t s.val ht (hJ s.val s.property) (hJF s.property) x.val =
      boxTransport F b t s.val ht (hJ s.val s.property) (hJF s.property) y.val :=
    sigma_mk_injective (i := s.val) hxy
  exact Prod.ext rfl (Subtype.ext
    ((boxTransport_leftInverse F b t s.val ht (hJ s.val s.property)
      htF (hJF s.property)).injOn x.property y.property hval))

end PoincareConjecture.M28
