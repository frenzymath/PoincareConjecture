import PoincareConjecture.Proofs.M76.Horizon.CompactCore.General.OriginalComponentEssentialPolygon
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Loops.PolygonSquareRim
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.ComponentLoopReflection
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup











set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1




theorem exists_original_frontier_essential_rim
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (C : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    {S F : Set X} (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    (HC : (A.edgeComponentComplex C).space ≃ₜ S) (g : E → X)
    (hHC : ∀ z, (HC z : X) = g z)
    (hgPL : PolyhedralPLInCharts e g (A.edgeComponentComplex C).space)
    (hpositive : Nat.card (A.edgeComponentComplex C).vertices +
      Nat.card (Triangle (A.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex) <
      Nat.card (Edge (A.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)) (a : Q ≃ₜ P.boundary ℝ)
      (d : V2 → E) (gamma : C(Q, F)),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
      (∀ i, P.edgeVertices i ∈ (A.edgeComponentComplex C).faces) ∧
      P.boundary ℝ ⊆ (A.edgeComponentComplex C).space ∧
      a.IsFinitePL ∧ FinitePiecewiseAffineOn d Q ∧
      (∀ x : Q, d x = (a x : E)) ∧ d '' Q = P.boundary ℝ ∧
      (∀ x : Q, (gamma x : X) = g (d x)) ∧
      (∀ x : Q, (gamma x : X) ∈ S) ∧
      Topology.IsEmbedding gamma ∧ PolyhedralPLInCharts e (g ∘ d) Q ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  classical
  let J := A.edgeComponentComplex C
  let : Fintype J.vertices :=
    (J.finite_vertices_of_finite_faces (hA.subset (A.edgeComponentComplex_le C))).fintype
  obtain ⟨z, hz, v, c, hc, hvalue, n, P, hbase, hsub, hlen, hvertices,
    hinj, hP, hfaces, _⟩ :=
    A.exists_edgeComponent_essential_polygon hA C hpure hcofaces hlinks hpositive
  obtain ⟨a, d, rim, hzero, ha, hd, had, hrim, himage, hemb, hloop⟩ :=
    Dehn.exists_original_polygon_square_rim J c P hlen hvertices hbase hP hinj hsub
  let mark : C(J.space, S) := ⟨HC, HC.continuous⟩
  let rimS : C(Q, S) := mark.comp rim
  let gamma : C(Q, F) := (ContinuousMap.inclusion hSF).comp rimS
  have hgamma (x : Q) : (gamma x : X) = g (d x) := by
    exact (hHC (rim x)).trans (congrArg g (hrim x))
  have hmap : MapsTo d Q J.space := by
    intro x hx
    rw [had ⟨x, hx⟩]
    exact hsub (a ⟨x, hx⟩).property
  have hPL : PolyhedralPLInCharts e (g ∘ d) Q := by
    obtain ⟨K, hK, hKQ, hKd⟩ := hd
    have h := hgPL.comp_finitePiecewiseAffineOn K hK
      (hKd.finitePiecewiseAffineOn hK) (hKQ ▸ hmap)
    exact hKQ ▸ h
  have hnontrivial : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
    intro htrivial
    have hnull : (Dehn.squareRimLoop.map gamma.continuous).Homotopic (Path.refl _) :=
      Path.Homotopic.Quotient.exact htrivial
    have hnullF : ((Dehn.squareRimLoop.map rimS.continuous).map
        (continuous_inclusion hSF)).Homotopic
        ((Path.refl (rimS Dehn.squareRimBase)).map (continuous_inclusion hSF)) := hnull
    have hnullS := Path.Homotopic.of_map_whole_component hSF hcomponent hnullF
    have hnullHC : ((Dehn.squareRimLoop.map rim.continuous).map HC.continuous).Homotopic
        ((Path.refl (rim Dehn.squareRimBase)).map HC.continuous) := hnullS
    have hnullJ := Path.Homotopic.of_map_homeomorph HC hnullHC
    have hgeo := J.geometricWalk_not_homotopic_refl_of_value_ne_zero
      (cocycleOfClosed J.vertexAbstractComplex.toPreAbstractSimplicialComplex z hz)
      c (by rw [hvalue]; exact one_ne_zero)
    exact hgeo (hloop.symm.trans (hnullJ.cast_refl hzero.symm))
  refine ⟨n, P, a, d, gamma, hP, hinj, hfaces, hsub, ha, hd, had, himage,
    hgamma, (fun x => (HC (rim x)).property), ?_, hPL, hnontrivial⟩
  exact (Topology.IsEmbedding.inclusion hSF).comp (HC.isEmbedding.comp hemb)

end PoincareConjecture.M76
