import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusPairedCycles
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalGraphEdges

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
  {A : AbstractSimplicialComplex V}

abbrev ResidualEdge (L : Finset (Edge A.toPreAbstractSimplicialComplex)) :=
  {e : Edge A.toPreAbstractSimplicialComplex // e ∈ L}

abbrev OriginalTorusBoundarySide (P : SimpleGraph V)
    (L : Finset (Edge A.toPreAbstractSimplicialComplex)) :=
  (P.edgeSet ⊕ ResidualEdge L) × Bool

structure OriginalTorusBoundarySideInventory
    (P : SimpleGraph V)
    (L : Finset (Edge A.toPreAbstractSimplicialComplex)) where
  hP : P ≤ A.edgeGraph
  sideEdge : OriginalTorusBoundarySide (A := A) P L →
      Edge A.toPreAbstractSimplicialComplex
  sideEdge_primal : ∀ (s : OriginalTorusBoundarySide (A := A) P L)
      (p : P.edgeSet),
      s.1 = Sum.inl p →
      sideEdge s = (A.originalGraphEdgeEquiv P hP p).val
  sideEdge_residual : ∀ (s : OriginalTorusBoundarySide (A := A) P L)
      (r : ResidualEdge (A := A) L),
      s.1 = Sum.inr r → sideEdge s = r.val
  opposite : OriginalTorusBoundarySide (A := A) P L →
      OriginalTorusBoundarySide (A := A) P L
  opposite_first : ∀ s, (opposite s).1 = s.1
  opposite_second : ∀ s, (opposite s).2 = !s.2
  opposite_involutive : Function.Involutive opposite

namespace OriginalTorusBoundarySideInventory

variable {P : SimpleGraph V}
  {L : Finset (Edge A.toPreAbstractSimplicialComplex)}

@[simp] theorem opposite_sideEdge_label
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (s : OriginalTorusBoundarySide (A := A) P L) :
    (I.opposite s).1 = s.1 :=
  I.opposite_first s

@[simp] theorem opposite_side
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (s : OriginalTorusBoundarySide (A := A) P L) :
    (I.opposite s).2 = !s.2 :=
  I.opposite_second s

theorem opposite_ne
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (s : OriginalTorusBoundarySide (A := A) P L) :
    I.opposite s ≠ s := by
  intro h
  have hb : (!s.2 : Bool) = s.2 := by
    rw [← I.opposite_second s, h]
  cases hs : s.2 <;> simp [hs] at hb

theorem opposite_preserves_original_edge
    (I : OriginalTorusBoundarySideInventory (A := A) P L)
    (s : OriginalTorusBoundarySide (A := A) P L) :
    I.sideEdge (I.opposite s) = I.sideEdge s := by
  rcases s with ⟨label, sign⟩
  rcases label with p | r
  · have hleft := I.sideEdge_primal (Sum.inl p, !sign) p rfl
    have hright := I.sideEdge_primal (Sum.inl p, sign) p rfl
    have hop : I.opposite (Sum.inl p, sign) = (Sum.inl p, !sign) := by
      apply Prod.ext
      · exact I.opposite_first _
      · exact I.opposite_second _
    rw [hop]
    exact hleft.trans hright.symm
  · have hleft := I.sideEdge_residual (Sum.inr r, !sign) r rfl
    have hright := I.sideEdge_residual (Sum.inr r, sign) r rfl
    have hop : I.opposite (Sum.inr r, sign) = (Sum.inr r, !sign) := by
      apply Prod.ext
      · exact I.opposite_first _
      · exact I.opposite_second _
    rw [hop]
    exact hleft.trans hright.symm

theorem exists_of_trees_and_residual
    (P : SimpleGraph V)
    (L : Finset (Edge A.toPreAbstractSimplicialComplex))
    (hP : P ≤ A.edgeGraph) :
    Nonempty (OriginalTorusBoundarySideInventory (A := A) P L) := by
  let edgeEquiv := A.originalGraphEdgeEquiv P hP
  let sideEdge : OriginalTorusBoundarySide (A := A) P L →
      Edge A.toPreAbstractSimplicialComplex :=
    fun s => match s.1 with
      | Sum.inl p => (edgeEquiv p).val
      | Sum.inr r => r.val
  let opposite : OriginalTorusBoundarySide (A := A) P L →
      OriginalTorusBoundarySide (A := A) P L :=
    fun s => (s.1, !s.2)
  have hprimal (s : OriginalTorusBoundarySide (A := A) P L)
      (p : P.edgeSet) (hs : s.1 = Sum.inl p) :
      sideEdge s = (edgeEquiv p).val := by
    simp only [sideEdge, hs]
  have hresidual (s : OriginalTorusBoundarySide (A := A) P L)
      (r : ResidualEdge (A := A) L) (hs : s.1 = Sum.inr r) :
      sideEdge s = r.val := by
    simp only [sideEdge, hs]
  refine ⟨⟨hP, sideEdge, hprimal, hresidual, opposite, ?_, ?_, ?_⟩⟩
  · intro s
    rfl
  · intro s
    rfl
  · intro s
    cases s with
    | mk label sign =>
      simp only [opposite]
      cases sign <;> rfl

end OriginalTorusBoundarySideInventory

theorem exists_original_torus_boundary_inventory
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    [Fintype (A.edgeComponentComplex c).vertices]
    (hzero : (A.edgeComponentComplex c).surfaceEulerCount = 0) :
    ∃ (P : SimpleGraph (A.edgeComponentComplex c).vertices)
      (D : SimpleGraph (Triangle
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex))
      (L : Finset (Edge
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex)),
      P ≤ (A.edgeComponentComplex c).vertexAbstractComplex.edgeGraph ∧
      P.IsTree ∧
      D ≤ complementaryTriangleGraph
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P ∧
      D.IsTree ∧ L.card = 2 ∧
      Nonempty (OriginalTorusBoundarySideInventory
        (A := (A.edgeComponentComplex c).vertexAbstractComplex) P L) := by
  obtain ⟨P, D, L, s₀, s₁, hP, hPtree, hD, hDtree, hLcard,
      hs₀not, hs₁not, hsneq, hpair₀, hpair₁⟩ :=
    exists_original_torus_two_paired_cycles A hA hpure hcofaces hlinks c hzero
  refine ⟨P, D, L, hP, hPtree, hD, hDtree, hLcard, ?_⟩
  exact OriginalTorusBoundarySideInventory.exists_of_trees_and_residual
    P L hP

end PoincareConjecture.M76
