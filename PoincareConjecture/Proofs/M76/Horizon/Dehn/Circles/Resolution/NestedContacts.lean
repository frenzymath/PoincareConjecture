import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.CollarGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.NestedAnnulusSource

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.PairedCircleCollars

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
  {D : OrdinaryIntervalMarkedModel old i} {L d : ℝ}

theorem nested_contacts (G : PairedCircleCollars D L d) (j : Fin 2)
    (hnest : closure (G.collar j.rev).outer.inside ⊆ (G.collar j).inner.inside) :
    (G.source 0 ∪ G.source 1) ∩ (D2 \ (G.collar j).outer.inside) =
        (G.collar j).outer.boundary ℝ ∧
      (G.source 0 ∪ G.source 1) ∩ closure (G.collar j.rev).inner.inside =
        (G.collar j.rev).inner.boundary ℝ := by
  have hparts (k : Fin 2) := _root_.Dehn.nested_annulus_source_partition
    (G.collar k).outer (G.collar k).inner
    (G.collar k).outer_simplicial (G.collar k).outer_injective
    (G.collar k).inner_simplicial (G.collar k).inner_injective
    (G.boundaries_interior k).1 (G.collar k).nested
  have hsource (k : Fin 2) : G.source k ⊆ closure (G.collar k).outer.inside :=
    (G.collar k).carrier.subset.trans sdiff_subset
  have hin : closure (G.collar j.rev).inner.inside ⊆ (G.collar j).inner.inside :=
    (G.collar j.rev).nested.trans (subset_closure.trans hnest)
  have hunion : G.source 0 ∪ G.source 1 = G.source j ∪ G.source j.rev := by
    fin_cases j
    · rfl
    · exact union_comm _ _
  rw [hunion]
  constructor
  · have hseam := (hparts j).2.2.1
    rw [← (G.collar j).carrier] at hseam
    ext x
    constructor
    · rintro ⟨hx | hx, ho⟩
      · exact hseam.subset ⟨hx, ho⟩
      · exact False.elim (ho.2 ((G.collar j).nested
          (subset_closure (hnest (hsource j.rev hx)))))
    · intro hx
      exact ⟨Or.inl (hseam.symm.subset hx).1, (hseam.symm.subset hx).2⟩
  · have hseam := (hparts j.rev).2.1
    rw [← (G.collar j.rev).carrier] at hseam
    ext x
    constructor
    · rintro ⟨hx | hx, hi⟩
      · exact False.elim (((G.collar j).carrier.subset hx).2 (hin hi))
      · exact hseam.subset ⟨hi, hx⟩
    · intro hx
      exact ⟨Or.inr (hseam.symm.subset hx).2, (hseam.symm.subset hx).1⟩

end PoincareConjecture.M76.Dehn.PairedCircleCollars
