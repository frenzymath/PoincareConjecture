import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.EmbeddedThreeSectionCenters

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u

namespace Poincare.Topology

structure EmbeddedThreeFlagGrid
    {N : Nat} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (e : C(M, EuclideanSpace Real (Fin N))) (epsilon : NNReal) where
  ambient_dimension : 3 < N
  injective : Function.Injective e
  tangent_dimension : ∀ p : M, Module.finrank Real (embeddedThreeTangent e p) = 3
  epsilon_pos : 0 < epsilon
  epsilon_small : (epsilon : Real) ≤ ambientGridGap N (N - 4) / (1000 * (N + 1))
  h : Real
  h_pos : 0 < h
  rho : Real
  radius_lt : 6 * (N + 1 : Real) * h < rho
  K : Geometry.SimplicialComplex Real (EuclideanSpace Real (Fin N))
  finite : Set.Finite K.faces
  cover : ∀ x, infDist x (Set.range e) ≤ 10 * (N + 1 : Real) * h → x ∈ K.space
  geometry : ∀ s ∈ K.faces, s.card ≤ N + 1 ∧
    diam (convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) ≤
      2 * (N + 1 : Real) * h ∧
    (2 ≤ s.card → ∀ v ∈ s,
      h / 4 ≤ infDist v
        (affineSpan Real ((s.erase v : Finset (EuclideanSpace Real (Fin N))) :
          Set (EuclideanSpace Real (Fin N))) : Set (EuclideanSpace Real (Fin N))))
  gap : ∀ s ∈ K.faces, s.card + 3 ≤ N →
    ∀ x ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N))),
      ambientGridGap N (N - 4) * h < infDist x (Set.range e)
  charts : ∀ p : M, ∃ g : OpenPartialHomeomorph (embeddedThreeTangent e p) M,
    g.source = ball 0 (2 * rho) ∧ g 0 = p ∧
    (∀ v ∈ g.source,
      (embeddedThreeTangent e p).orthogonalProjectionOnto (e (g v) - e p) = v) ∧
    LipschitzOnWith epsilon (fun v : embeddedThreeTangent e p =>
      e (g v) - e p - (v : EuclideanSpace Real (Fin N))) g.source ∧
    (∀ q : M, dist (e q) (e p) < rho → q ∈ g.target)
  centers : ∀ s ∈ K.faces,
    (∃ q : M, e q ∈ convexHull Real (s : Set (EuclideanSpace Real (Fin N)))) →
    N - 2 ≤ s.card ∧
    ∃ w : EuclideanSpace Real (Fin N) → Real,
      (∀ v ∈ s, ambientGridGap N (N - 4) /
        (2 * (N + 1 : Real) * (2 : Real) ^ (N + 1)) ≤ w v) ∧
      (∑ v ∈ s, w v) = 1 ∧
      (∑ v ∈ s, w v • v) = finiteSectionCenter (Set.range e) (N - 2) s

theorem exists_embedded_three_flag_grid
    {N : Nat} (hN : 3 < N) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (he : _root_.Topology.IsClosedEmbedding e)
    (hi : ∀ p : M, Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p))
    (epsilon : NNReal) (hepsilon : 0 < epsilon)
    (heps : (epsilon : Real) ≤ ambientGridGap N (N - 4) / (1000 * (N + 1)))
    (hmax : Real) (hhmax : 0 < hmax) :
    ∃ G : EmbeddedThreeFlagGrid e epsilon, G.h < hmax := by
  obtain ⟨h, hh, hhhmax, rho, _, hRrho, K, hfinite, hcover, hgeom, hgap,
      hcharts, hcenters, _⟩ :=
    exists_embedded_three_section_centers hN e hs he hi epsilon hepsilon heps hmax hhmax
  refine ⟨{
    ambient_dimension := hN
    injective := he.injective
    tangent_dimension := fun p => embeddedThreeTangent_finrank e p (hi p)
    epsilon_pos := hepsilon
    epsilon_small := heps
    h := h
    h_pos := hh
    rho := rho
    radius_lt := hRrho
    K := K
    finite := hfinite
    cover := hcover
    geometry := hgeom
    gap := hgap
    charts := hcharts
    centers := ?_ }, hhhmax⟩
  intro s hsK hmeet
  obtain ⟨hrank, _, w, _, hsum, hpoint, hbound⟩ := hcenters s hsK hmeet
  exact ⟨hrank, w, hbound, hsum, hpoint⟩

end Poincare.Topology
