import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.CollarGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OriginalCollars








set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
  {D : OrdinaryIntervalMarkedModel old i} {L d : ℝ}

theorem PairedCircleCollars.source_cases_retention (G : PairedCircleCollars D L d) :
    closure (G.collar 1).outer.inside ⊆ (G.collar 0).inner.inside ∨
      closure (G.collar 0).outer.inside ⊆ (G.collar 1).inner.inside ∨
      Disjoint (closure (G.collar 0).outer.inside)
        (closure (G.collar 1).outer.inside) := by
  exact G.source_cases

theorem PairedCircleCollars.component_geometry (G : PairedCircleCollars D L d)
    (hd : 0 < d) (j : Fin 2) :
    old.pieces (if j = 0 then i else old.mate i) ⊆
        (G.collar j).outer.inside \ closure (G.collar j).inner.inside ∧
      Disjoint (doubleLocusOn f D2)
        ((G.collar j).outer.boundary ℝ ∪ (G.collar j).inner.boundary ℝ) ∧
      ∀ k, k ≠ (if j = 0 then i else old.mate i) →
        Disjoint (old.pieces k)
          (closure (G.collar j).outer.inside \ (G.collar j).inner.inside) := by
  exact D.actual_collar_component_geometry j hd (G.collar j).chart
    (G.source_clip j) (G.middle_image j) (G.collar j).outer (G.collar j).inner
    (G.collar j).outer_simplicial (G.collar j).outer_injective
    (G.collar j).inner_simplicial (G.collar j).inner_injective
    (G.collar j).nested (G.collar j).carrier false
    (G.collar j).outer_depth (G.collar j).inner_depth

theorem PairedCircleCollars.selected_disjoint_rim (G : PairedCircleCollars D L d)
    (j : Fin 2) : Disjoint (old.pieces (if j = 0 then i else old.mate i)) Q2 := by
  apply disjoint_left.mpr
  intro x hx hq
  obtain ⟨p, _, rfl⟩ := (G.middle_image j).symm.subset hx
  exact disjoint_left.mp sphere_disjoint_ball.symm
    (G.source_interior j ((G.collar j).chart p).property) hq

theorem PairedCircleCollars.nested_retention (G : PairedCircleCollars D L d)
    (hd : 0 < d) (j : Fin 2)
    (hnested : closure (G.collar j.rev).outer.inside ⊆ (G.collar j).inner.inside) :
    let K := closure (G.collar j.rev).inner.inside ∪ (D2 \ (G.collar j).outer.inside)
    (∀ k, old.pieces k ⊆ K ∨ Disjoint (old.pieces k) K) ∧
      Disjoint (old.pieces (if j = 0 then i else old.mate i) ∪
        old.pieces (if j.rev = 0 then i else old.mate i)) K ∧
      ¬ old.pieces (if j = 0 then i else old.mate i) ⊆ K ∧
      ¬ old.pieces (if j.rev = 0 then i else old.mate i) ⊆ K ∧
      Disjoint (K ∩ doubleLocusOn f D2)
        (closure (G.collar j).outer.inside \ (G.collar j.rev).inner.inside) := by
  obtain ⟨hs₀, hb₀, ha₀⟩ := G.component_geometry hd j
  obtain ⟨hs₁, hb₁, ha₁⟩ := G.component_geometry hd j.rev
  exact old.nested_collar_retention _ _
    (G.collar j).outer (G.collar j).inner
    (G.collar j.rev).outer (G.collar j.rev).inner
    (G.collar j).outer_simplicial (G.collar j).outer_injective
    (G.collar j).inner_simplicial (G.collar j).inner_injective
    (G.collar j.rev).inner_simplicial (G.collar j.rev).inner_injective
    (G.collar j).nested (G.collar j.rev).nested hnested hs₀ hs₁ ha₀ ha₁ hb₀ hb₁

theorem PairedCircleCollars.disjoint_retention (G : PairedCircleCollars D L d)
    (hd : 0 < d)
    (hdis : Disjoint (closure (G.collar 0).outer.inside)
      (closure (G.collar 1).outer.inside)) :
    let K := (closure (G.collar 0).inner.inside ∪ closure (G.collar 1).inner.inside) ∪
      (D2 \ ((G.collar 0).outer.inside ∪ (G.collar 1).outer.inside))
    (∀ k, old.pieces k ⊆ K ∨ Disjoint (old.pieces k) K) ∧
      (∀ k, k ≠ i → k ≠ old.mate i → old.pieces k ⊆ K) ∧
      Disjoint (old.pieces i ∪ old.pieces (old.mate i)) K ∧
      ¬ old.pieces i ⊆ K ∧ ¬ old.pieces (old.mate i) ⊆ K ∧
      Disjoint (K ∩ doubleLocusOn f D2)
        ((closure (G.collar 0).outer.inside \ (G.collar 0).inner.inside) ∪
          (closure (G.collar 1).outer.inside \ (G.collar 1).inner.inside)) := by
  obtain ⟨hs₀, hb₀, ha₀⟩ := G.component_geometry hd 0
  obtain ⟨hs₁, hb₁, ha₁⟩ := G.component_geometry hd 1
  simpa only [ite_true, ite_false, Fin.isValue, zero_ne_one, one_ne_zero] using
    old.disjoint_collar_retention i (old.mate i)
      (G.collar 0).outer (G.collar 0).inner
      (G.collar 1).outer (G.collar 1).inner
      (G.collar 0).outer_simplicial (G.collar 0).outer_injective
      (G.collar 0).inner_simplicial (G.collar 0).inner_injective
      (G.collar 1).outer_simplicial (G.collar 1).outer_injective
      (G.collar 1).inner_simplicial (G.collar 1).inner_injective
      (G.collar 0).nested (G.collar 1).nested hdis hs₀ hs₁ ha₀ ha₁ hb₀ hb₁

end PoincareConjecture.M76.Dehn
