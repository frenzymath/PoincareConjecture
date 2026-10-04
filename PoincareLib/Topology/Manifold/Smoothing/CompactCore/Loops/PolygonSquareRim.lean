import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polygons.Mathlib.SquarePolygonUniformBoundary
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polygons.Mathlib.UniformPolygonLoopHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Graphs.Mathlib.PolygonCycleLoopComparison

/-!
# The actual original polygon as a finite PL square rim

The constructed finite PL boundary homeomorphism preserves the original
cyclic vertices and all edges. Its fixed square-rim loop represents the
same original geometric cycle, without any disk-filling assumption.
See Wall019, lines 133--143, and Dehn025, sections 3--4.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

/-- Construct the square-rim parametrization of the actual polygon,
including its whole finite PL map and exact original cycle class. -/
theorem exists_original_polygon_square_rim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E)
    {v : K.vertices} (w : K.vertexAbstractComplex.edgeGraph.Walk v v)
    {n : ℕ} (P : Polygon E (n + 3)) (hlen : n + 3 = w.length)
    (hvertices : ∀ i : Fin (n + 3), P i = (w.getVert i.val : E))
    (hbase : P 0 = (v : E)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hsub : P.boundary ℝ ⊆ K.space) :
    ∃ (a : Q ≃ₜ P.boundary ℝ) (d : V2 → E) (rim : C(Q, K.space))
      (hzero : rim squareRimBase = (⟨v, K.vertices_subset_space v.property⟩ : K.space)),
      a.IsFinitePL ∧ FinitePiecewiseAffineOn d Q ∧
      (∀ x : Q, d x = (a x : E)) ∧
      (∀ x : Q, (rim x : E) = d x) ∧
      d '' Q = P.boundary ℝ ∧ Topology.IsEmbedding rim ∧
      ((squareRimLoop.map rim.continuous).cast hzero.symm hzero.symm).Homotopic
        (K.geometricWalkPath w) := by
  obtain ⟨a, ha, ha0, hformula⟩ := exists_square_polygon_uniform_boundary P hP hinj
  obtain ⟨d, hd, had⟩ := ha
  let incl : C(P.boundary ℝ, K.space) := ⟨Set.inclusion hsub, continuous_inclusion hsub⟩
  let rim : C(Q, K.space) := incl.comp ⟨a, a.continuous⟩
  have hzero : rim squareRimBase = (⟨v, K.vertices_subset_space v.property⟩ : K.space) :=
    Subtype.ext (ha0.trans hbase)
  have ha0' : a squareRimBase = (⟨P 0, P.vertex_mem_boundary 0⟩ : P.boundary ℝ) :=
    Subtype.ext ha0
  let sigma := (squareRimLoop.map a.continuous).cast ha0'.symm ha0'.symm
  have hsigma : sigma.Homotopic P.boundaryLoop :=
    P.homotopic_boundaryLoop_of_uniform sigma (fun i u s hs => hformula i u s hs)
  have hcycle := K.polygon_boundaryLoop_homotopic_geometricWalk
    w P hlen hvertices hbase hsub
  have hloop : ((squareRimLoop.map rim.continuous).cast hzero.symm hzero.symm).Homotopic
      (K.geometricWalkPath w) :=
    ((hsigma.map incl).pathCast (Subtype.ext hbase.symm) (Subtype.ext hbase.symm)).trans hcycle
  have himage : d '' Q = P.boundary ℝ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← had ⟨x, hx⟩]
      exact (a ⟨x, hx⟩).property
    · intro hy
      refine ⟨a.symm ⟨y, hy⟩, (a.symm ⟨y, hy⟩).property, ?_⟩
      rw [← had, a.apply_symm_apply]
  refine ⟨a, d, rim, hzero, ⟨d, hd, had⟩, hd, (fun x => (had x).symm),
    had, himage, ?_, hloop⟩
  exact (Topology.IsEmbedding.inclusion hsub).comp a.isEmbedding

end PoincareMT.M76.Dehn
