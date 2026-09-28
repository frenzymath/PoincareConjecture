import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.InnermostWithBoundaryArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.OneMarkedEnd



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Q₀" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Q₁" => Set.ofPred (fun x : P2 => depth 8 x = 1)
local notation "Rim" => Q₀ ∪ Q₁

theorem exists_innermost_disk_of_closed_intersection_component
    {κ : Type*} [Finite κ] (pieces : κ → Set P2)
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hsub : ∀ i, pieces i ⊆ {x : P2 | -1 ≤ depth 8 x ∧ depth 8 x ≤ 1})
    (hmodels : ∀ i, IsFinitePLBallPair ℝ (pieces i) (pieces i ∩ Rim) ∨
      ∃ (n : ℕ) (P : Polygon P2 (n + 3)), Function.Injective P ∧
        P.HasSimplicialEdges ∧ P.boundary ℝ = pieces i ∧ Disjoint (pieces i) Rim)
    (a : P2) (hfirst : (⋃ i, pieces i) ∩ Q₀ = {a})
    (hcircle : ∃ i, Disjoint (pieces i) Rim) :
    ∃ (i : κ) (n : ℕ) (P : Polygon P2 (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ = pieces i ∧
      IsFinitePLBallPair P2 (closure P.inside) (P.boundary ℝ) ∧
      closure P.inside ⊆ {x : P2 | -1 < depth 8 x ∧ depth 8 x < 1} ∧
      closure P.inside ∩ (⋃ j, pieces j) = P.boundary ℝ ∧
      Disjoint P.inside (⋃ j, pieces j) := by
  classical
  have hQ : Disjoint Q₀ Q₁ := disjoint_left.mpr fun x hx hy => by
    change depth 8 x = -1 at hx
    change depth 8 x = 1 at hy
    linarith
  obtain ⟨s,b,ha,hb,hab,hs,hsends,hs₀,hs₁,_,_⟩ :=
    exists_unique_spanning_interval_of_one_marked_point pieces Q₀ Q₁ a hQ hdis hfirst hmodels
  let C := {i : κ // Disjoint (pieces i) Rim}
  let A := {i : κ // ¬ Disjoint (pieces i) Rim}
  have : Nonempty C := by
    obtain ⟨i,hi⟩ := hcircle
    exact ⟨⟨i,hi⟩⟩
  have hcircles (i : C) : ∃ (n : ℕ) (P : Polygon P2 (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ P.boundary ℝ = pieces i := by
    rcases hmodels i with hi | ⟨n,P,hPi,hP,hPb,_⟩
    · obtain ⟨u,v,_,huv⟩ := hi.exists_boundary_eq_pair
      have hu := huv.symm.subset (show u ∈ ({u,v} : Set P2) from Or.inl rfl)
      exact (disjoint_left.mp i.property hu.1 hu.2).elim
    · exact ⟨n,P,hPi,hP,hPb⟩
  choose n P hPi hP hPb using hcircles
  have hcircboundary (i : C) (x : P2) (hx : x ∈ (P i).boundary ℝ) :
      -1 < depth 8 x ∧ depth 8 x < 1 := by
    have hxi := (hPb i).subset hx
    have hxB := hsub i hxi
    refine ⟨lt_of_le_of_ne hxB.1 ?_,lt_of_le_of_ne hxB.2 ?_⟩
    · intro hh
      exact disjoint_left.mp i.property hxi (Or.inl hh.symm)
    · intro hh
      exact disjoint_left.mp i.property hxi (Or.inr hh)
  have hcircdis : Pairwise (fun i j : C =>
      Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) := by
    intro i j hij
    rw [hPb i,hPb j]
    exact hdis (fun hh => hij (Subtype.ext hh))
  have hsc (i : C) : Disjoint (pieces s) ((P i).boundary ℝ) := by
    rw [hPb i]
    apply hdis
    intro hsi
    have has : a ∈ pieces s := hs.1 (Or.inl rfl)
    exact disjoint_left.mp i.property (hsi ▸ has) (Or.inl ha)
  have harcs (i : A) : IsFinitePLBallPair ℝ (pieces i) (pieces i ∩ Rim) := by
    rcases hmodels i with hi | ⟨_,_,_,_,_,hi⟩
    · exact hi
    · exact (i.property hi).elim
  have harcrim (i : A) : (pieces i ∩ Rim).Nonempty := by
    obtain ⟨u,v,_,huv⟩ := (harcs i).exists_boundary_eq_pair
    exact ⟨u,huv.symm.subset (Or.inl rfl)⟩
  have hac (i : A) (j : C) : Disjoint (pieces i) ((P j).boundary ℝ) := by
    rw [hPb j]
    apply hdis
    intro hij
    exact i.property (hij.symm ▸ j.property)
  obtain ⟨i,hball,hinside,_,_,hinter,havoid⟩ :=
    exists_innermost_circle_avoiding_boundary_arcs n P hP hPi hcircboundary hcircdis
      hs.isConnected.2 hsc ⟨a,hs.1 (Or.inl rfl),ha⟩ ⟨b,hs.1 (Or.inr rfl),hb⟩
      (fun i : A => pieces i) (fun i => (harcs i).isConnected.2) harcrim hac
  have hunion : (⋃ i : A, pieces i) ∪ (⋃ i : C, (P i).boundary ℝ) = ⋃ i, pieces i := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i,hi⟩
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i,(hPb i).subset hi⟩
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      by_cases hc : Disjoint (pieces i) Rim
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i,hc⟩,(hPb ⟨i,hc⟩).symm.subset hi⟩)
      · exact Or.inl (mem_iUnion.mpr ⟨⟨i,hc⟩,hi⟩)
  exact ⟨i,n i,P i,hPi i,hP i,hPb i,hball,hinside,
    hunion ▸ hinter,hunion ▸ havoid⟩

end PoincareConjecture.M76.Dehn.Annuli
