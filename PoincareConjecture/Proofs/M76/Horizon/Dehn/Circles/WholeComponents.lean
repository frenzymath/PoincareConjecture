import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ComponentRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.OriginalPairedSourceAnnuli

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

theorem OrdinaryIntervalMarkedModel.clip_inter_double_locus
    (D : OrdinaryIntervalMarkedModel old i) (j : Fin 2) :
    (D.clips j.castSucc).space ∩ doubleLocusOn f D2 =
      old.pieces (if j = 0 then i else old.mate i) := by
  have hinj (k : Fin 2) : InjOn f (D.source k.castSucc).space := by
    have he : IsEmbedding (fun x : (D.source k.castSucc).space ↦ f x) := by
      fin_cases k
      · exact D.left_embedding
      · exact D.right_embedding
    intro x hx y hy hxy
    exact congrArg Subtype.val (he.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  ext x
  constructor
  · rintro ⟨hxclip, hxdouble⟩
    have hxsource := ((D.clips_data j.castSucc).2.1.subset hxclip).1
    have hxcore := ((D.clips_data j.castSucc).2.1.subset hxclip).2
    let y := old.partner ⟨x, hxdouble⟩
    have hfy : f y = f x := old.partner_value ⟨x, hxdouble⟩
    have hycore : f y ∈ D.core := hfy ▸ hxcore
    have hysource := D.full_preimage y y.property.1 (D.core_subset hycore)
    have hyother : (y : V2) ∈ (D.source j.rev.castSucc).space := by
      fin_cases j
      · rcases hysource with hy0 | hy1
        · exact False.elim (old.partner_free ⟨x, hxdouble⟩
            (hinj 0 hy0 hxsource hfy))
        · exact hy1
      · rcases hysource with hy0 | hy1
        · exact hy0
        · exact False.elim (old.partner_free ⟨x, hxdouble⟩
            (hinj 1 hy1 hxsource hfy))
    have himages : f x ∈ f '' (D.source 0).space ∩ f '' (D.source 1).space := by
      fin_cases j
      · exact ⟨⟨x, hxsource, rfl⟩, ⟨y, hyother, hfy⟩⟩
      · exact ⟨⟨y, hyother, hfy⟩, ⟨x, hxsource, rfl⟩⟩
    have hphysical := D.intersection.subset ⟨D.core_subset hxcore, himages⟩
    have hpieces := (old.piece_image_preimage i x hxdouble.1).mp hphysical
    fin_cases j
    · rcases hpieces with hi | hm
      · exact hi
      · exact False.elim (disjoint_left.mp D.disjoint hxsource (D.right_contains hm))
    · rcases hpieces with hi | hm
      · exact False.elim (disjoint_left.mp D.disjoint (D.left_contains hi) hxsource)
      · exact hm
  · intro hx
    have hxdouble := old.piece_subset_double (if j = 0 then i else old.mate i) hx
    have hxsource : x ∈ (D.source j.castSucc).space := by
      fin_cases j
      · exact D.left_contains hx
      · exact D.right_contains hx
    have hphysical : f x ∈ f '' old.pieces i := by
      fin_cases j
      · exact mem_image_of_mem f hx
      · exact (old.piece_image_mate i).subset (mem_image_of_mem f hx)
    exact ⟨(D.clips_data j.castSucc).2.1.symm.subset
      ⟨hxsource, show f x ∈ D.core from interior_subset (D.core_neighborhood hphysical)⟩,
      hxdouble⟩

theorem OrdinaryIntervalMarkedModel.annuli_inter_double_locus
    (D : OrdinaryIntervalMarkedModel old i) (A : Fin 2 → Set V2)
    (hA : ∀ j, A j ⊆ (D.clips j.castSucc).space)
    (hselected : ∀ j, old.pieces (if j = 0 then i else old.mate i) ⊆ A j) :
    (∀ j, A j ∩ doubleLocusOn f D2 = old.pieces (if j = 0 then i else old.mate i)) ∧
      ∀ k, k ≠ i → k ≠ old.mate i → ∀ j, Disjoint (old.pieces k) (A j) := by
  have hinter (j : Fin 2) : A j ∩ doubleLocusOn f D2 =
      old.pieces (if j = 0 then i else old.mate i) := by
    apply Subset.antisymm
    · rintro x ⟨hx, hd⟩
      exact (D.clip_inter_double_locus j).subset ⟨hA j hx, hd⟩
    · intro x hx
      exact ⟨hselected j hx, old.piece_subset_double _ hx⟩
  refine ⟨hinter, ?_⟩
  intro k hki hkm j
  apply disjoint_left.mpr
  intro x hx hxA
  have hxs := (hinter j).subset ⟨hxA, old.piece_subset_double k hx⟩
  fin_cases j
  · exact disjoint_left.mp (old.disjoint hki) hx hxs
  · exact disjoint_left.mp (old.disjoint hkm) hx hxs

end PoincareConjecture.M76.Dehn
