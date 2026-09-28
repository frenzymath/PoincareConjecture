import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.SelectedComponent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedCounts

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.SourceCircleDecomposition



theorem retained_component_count_lt
    {E Y X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Y] [T2Space Y]
    {f : E → X} {g : Y → X} {S K : Set E} {T : Set Y}
    (M : SourceCircleDecomposition f S) (hKS : K ⊆ S)
    (hwhole : ∀ i, M.pieces i ⊆ K ∨ Disjoint (M.pieces i) K)
    (j : K → Y) (hji : Function.Injective j) (hjc : Continuous j)
    (hnew : doubleLocusOn g T =
      j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y})
    (i : M.Index) (hremoved : ¬ M.pieces i ⊆ K) :
    Nat.card (ConnectedComponents (doubleLocusOn g T)) <
      Nat.card (ConnectedComponents (doubleLocusOn f S)) := by
  classical
  let : Finite M.Index := M.finite_components
  have hdec := retained_double_component_interior_counts_decrease
    (G := M.graph.space) (G' := doubleLocusOn g T) (Q := (∅ : Set E)) (Q' := (∅ : Set Y))
    M.pieces M.mate M.partner M.space M.cover.symm
    M.pieces_isCompact M.pieces_isConnected M.disjoint
    (fun x ↦ (M.value x).symm) (fun x ↦ Ne.symm (M.free x))
    (fun x y hy hxy hne ↦ M.unique x y hy hne hxy)
    (fun k x hx ↦ (M.partner_component k x).mp hx)
    hKS hwhole j hji hjc hnew (fun _ ↦ by simp) i (by simp) hremoved
  have hlt := hdec.2
  simp only [preimage_empty, image_empty, compl_empty, Set.ncard_univ] at hlt
  change Nat.card (ConnectedComponents (doubleLocusOn g T)) <
    Nat.card (ConnectedComponents M.graph.space) at hlt
  rw [M.space] at hlt
  exact hlt

end PoincareConjecture.M76.Dehn.Annuli.SourceCircleDecomposition
