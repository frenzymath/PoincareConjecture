import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusResidualEdges
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Graphs.Mathlib.ResidualPairedCycles











set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical

def PairedCycleData
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : AbstractSimplicialComplex V)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (P : SimpleGraph V)
    (D : SimpleGraph (Triangle A.toPreAbstractSimplicialComplex))
    (s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet) : Prop :=
  ∃ (v : V) (c : A.edgeGraph.Walk v v)
    (t : Triangle A.toPreAbstractSimplicialComplex)
    (d : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).Walk t t),
    c.IsCycle ∧ d.IsCycle ∧
      (∃ p ∈ c.edges,
        p.toFinset = (complementaryTriangleEdgeEquiv
          A.toPreAbstractSimplicialComplex P hcofaces s).val.val) ∧
      s.val ∈ d.edges ∧
      (∀ p ∈ c.edges,
        p ∈ P.edgeSet ∨ p.toFinset =
          (complementaryTriangleEdgeEquiv
            A.toPreAbstractSimplicialComplex P hcofaces s).val.val) ∧
      (∀ r ∈ d.edges, r ∈ D.edgeSet ∨ r = s.val) ∧
      (∀ f : Edge A.toPreAbstractSimplicialComplex,
        ((∃ p ∈ c.edges, p.toFinset = f.val) ∧
          ∃ r : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet,
            r.val ∈ d.edges ∧
              (complementaryTriangleEdgeEquiv
                A.toPreAbstractSimplicialComplex P hcofaces r).val = f) ↔
          f = (complementaryTriangleEdgeEquiv
            A.toPreAbstractSimplicialComplex P hcofaces s).val)

theorem exists_original_torus_two_paired_cycles
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
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex))
      (s₀ s₁ : (complementaryTriangleGraph
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet),
      P ≤ (A.edgeComponentComplex c).vertexAbstractComplex.edgeGraph ∧
      P.IsTree ∧
      D ≤ complementaryTriangleGraph
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P ∧
      D.IsTree ∧ L.card = 2 ∧
      s₀.val ∉ D.edgeSet ∧ s₁.val ∉ D.edgeSet ∧ s₀ ≠ s₁ ∧
      PairedCycleData
        (A.edgeComponentComplex c).vertexAbstractComplex
        (A.edgeComponentComplex_triangle_cofaces c hcofaces) P D s₀ ∧
      PairedCycleData
        (A.edgeComponentComplex c).vertexAbstractComplex
        (A.edgeComponentComplex_triangle_cofaces c hcofaces) P D s₁ := by
  obtain ⟨P, hP, hPtree, D, hD, hDtree, L, hL, hLnot, hcard⟩ :=
    exists_original_torus_residual_edges A hA hpure hcofaces hlinks c hzero
  obtain ⟨e₀, e₁, he01, hLeq⟩ := Finset.card_eq_two.mp hcard
  have he₀L : e₀ ∈ L := by rw [hLeq]; simp
  have he₁L : e₁ ∈ L := by rw [hLeq]; simp
  obtain ⟨s₀, hs₀eq, hs₀not⟩ := (hL e₀).mp he₀L
  obtain ⟨s₁, hs₁eq, hs₁not⟩ := (hL e₁).mp he₁L
  have hsneq : s₀ ≠ s₁ := by
    intro hs
    apply he01
    exact hs₀eq.symm.trans ((congrArg Subtype.val (congrArg
      (complementaryTriangleEdgeEquiv
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex P
        (A.edgeComponentComplex_triangle_cofaces c hcofaces)) hs)).trans hs₁eq)
  have hPconn : P.Connected := hPtree.connected
  have hDconn : D.Connected := hDtree.connected
  have hpair₀ := AbstractSimplicialComplex.exists_paired_cycles_of_residual_edge
    (A.edgeComponentComplex c).vertexAbstractComplex
    (A.edgeComponentComplex_triangle_cofaces c hcofaces)
    P hP hPconn D hD hDconn s₀ hs₀not
  have hpair₁ := AbstractSimplicialComplex.exists_paired_cycles_of_residual_edge
    (A.edgeComponentComplex c).vertexAbstractComplex
    (A.edgeComponentComplex_triangle_cofaces c hcofaces)
    P hP hPconn D hD hDconn s₁ hs₁not
  exact ⟨P, D, L, s₀, s₁, hP, hPtree, hD, hDtree, hcard,
    hs₀not, hs₁not, hsneq, hpair₀, hpair₁⟩

end PoincareConjecture.M76
