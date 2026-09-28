import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonDiskSquareNormalization
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.UniformPolygonLoopHomotopy
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonCycleLoopComparison












set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1





theorem exists_marked_normalized_polygon_disk
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [TopologicalSpace X] (K : SimplicialComplex ℝ E)
    {v : K.vertices} (w : K.vertexAbstractComplex.edgeGraph.Walk v v)
    {n : ℕ} (P : Polygon E (n + 3)) (hlen : n + 3 = w.length)
    (hvertices : ∀ i : Fin (n + 3), P i = (w.getVert i.val : E))
    (hbase : P 0 = (v : E)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hsub : P.boundary ℝ ⊆ K.space)
    {b : Set E} (hb : IsFinitePLBallPair (ℝ × ℝ) b (P.boundary ℝ))
    (mark : C(K.space, X)) {base : X}
    (p : Path base (mark ⟨v, K.vertices_subset_space v.property⟩))
    (J : Subgroup (FundamentalGroup X base))
    (houtside : p.whiskeredLoopClass ((K.geometricWalkPath w).map mark.continuous) ∉ J) :
    ∃ (e : Q ≃ₜ P.boundary ℝ) (d : V2 → E) (rim : C(Q, X))
      (p' : Path base (rim squareRimBase)),
      e.IsFinitePL ∧ FinitePiecewiseAffineOn d D ∧
      Topology.IsEmbedding (fun x : D => d x) ∧ d '' D = b ∧
      (∀ x : Q, d x = (e x : E)) ∧
      (∀ x : D, d x ∈ P.boundary ℝ ↔ (x : V2) ∈ Q) ∧
      (∀ x : Q, rim x = mark ⟨e x, hsub (e x).property⟩) ∧
      (∀ t, p' t = p t) ∧ p'.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J := by
  obtain ⟨e, d, he, hd, hemb, himage, hrim, hiff, he0, hformula⟩ :=
    exists_normalized_polygon_disk P hP hinj hb
  let incl : C(P.boundary ℝ, K.space) := ⟨Set.inclusion hsub, continuous_inclusion hsub⟩
  let rim : C(Q, X) := mark.comp (incl.comp ⟨e, e.continuous⟩)
  have hq0 : rim squareRimBase = mark ⟨v, K.vertices_subset_space v.property⟩ :=
    congrArg mark (Subtype.ext (he0.trans hbase))
  let p' : Path base (rim squareRimBase) := p.cast rfl hq0
  have heq0 : e squareRimBase = (⟨P 0, P.vertex_mem_boundary 0⟩ : P.boundary ℝ) :=
    Subtype.ext he0
  let sigma := (squareRimLoop.map e.continuous).cast heq0.symm heq0.symm
  have hsigma : sigma.Homotopic P.boundaryLoop :=
    P.homotopic_boundaryLoop_of_uniform sigma (fun i u s hs => hformula i u s hs)
  have hcycle := K.polygon_boundaryLoop_homotopic_geometricWalk
    w P hlen hvertices hbase hsub
  have hmarked := (((hsigma.map incl).pathCast
    (Subtype.ext hbase.symm) (Subtype.ext hbase.symm)).trans hcycle).map mark
  have hloop : ((squareRimLoop.map rim.continuous).cast hq0.symm hq0.symm).Homotopic
      ((K.geometricWalkPath w).map mark.continuous) := hmarked
  have hclass : p'.whiskeredLoopClass (squareRimLoop.map rim.continuous) =
      p.whiskeredLoopClass ((K.geometricWalkPath w).map mark.continuous) :=
    Path.Homotopic.Quotient.eq.mpr
      (((Path.Homotopic.refl p).hcomp hloop).hcomp (Path.Homotopic.refl p.symm))
  refine ⟨e, d, rim, p', he, hd, hemb, himage, hrim, hiff,
    fun _ => rfl, fun _ => rfl, ?_⟩
  rw [hclass]
  exact houtside

end PoincareConjecture.M76.Dehn
