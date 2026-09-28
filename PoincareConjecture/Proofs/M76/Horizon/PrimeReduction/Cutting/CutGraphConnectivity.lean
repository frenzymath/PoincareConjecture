import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphSectionPasting
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Logic.Relation









set_option autoImplicit false

namespace PoincareConjecture.M76.CutGraph

variable {V I X : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  [TopologicalSpace X] [PreconnectedSpace X]

theorem incidence_connected_of_vertices_reached (ends : I → Bool → V)
    (q : C(X, carrier ends))
    (hq : ∀ v, ∃ x, (q x : Ambient V I) = vertex v) :
    ∀ v w, Relation.EqvGen
      (fun a b => ∃ i, ends i false = a ∧ ends i true = b) v w := by
  classical
  intro v w
  let rel := Relation.EqvGen
    (fun a b => ∃ i, ends i false = a ∧ ends i true = b)
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := ⟨rfl⟩
  let a : V → Bool := fun u => decide (rel v u)
  let u : I → Bool → Bool := fun i b => a (ends i b)
  have hab (i : I) : a (ends i false) = a (ends i true) := by
    have hi : rel (ends i false) (ends i true) :=
      Relation.EqvGen.rel _ _ ⟨i, rfl, rfl⟩
    change decide (rel v (ends i false)) = decide (rel v (ends i true))
    rw [decide_eq_decide]
    exact ⟨fun h => Relation.EqvGen.trans _ _ _ h hi,
      fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hi)⟩
  let arms : ∀ i b, Path (a (ends i b)) (u i b) := fun i b => Path.refl _
  let cores : ∀ i, Path (u i false) (u i true) := fun i =>
    (Path.refl (u i false)).cast rfl (hab i).symm
  obtain ⟨F, hF, _, _⟩ := exists_subdivided_path_map ends a u arms cores
  obtain ⟨x, hx⟩ := hq v
  obtain ⟨y, hy⟩ := hq w
  have he : F (q x) = F (q y) :=
    TotallyDisconnectedSpace.eq_of_continuous (F ∘ q) (F.continuous.comp q.continuous) x y
  rw [hF v (q x) hx, hF w (q y) hy] at he
  have hv : a v = true := by simp [a, rel, Relation.EqvGen.refl]
  have hw : a w = true := he.symm.trans hv
  exact of_decide_eq_true hw

end PoincareConjecture.M76.CutGraph
