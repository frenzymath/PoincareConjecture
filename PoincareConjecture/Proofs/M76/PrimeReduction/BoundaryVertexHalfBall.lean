import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryDualBall









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K L : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype L.faces]



structure BoundaryVertexHalfBall (p : E) where
  body : Set V3
  height : V3 →ₗ[ℝ] ℝ
  normal : V3
  chart : (K.barycentricDualBlock {p}).space ≃ₜ
    (body ∩ {x | 0 ≤ height x} : Set V3)
  normalized : height normal = 1
  compact : IsCompact body
  convex : Convex ℝ body
  center : (0 : V3) ∈ interior body
  polyhedral : ∃ J : SimplicialComplex ℝ V3, J.faces.Finite ∧ J.space = body
  ball : IsFinitePLBallPair V3 (K.barycentricDualBlock {p}).space
    (((K.barycentricDualBlock {p}).link p).space ∪ (L.barycentricDualBlock {p}).space)
  piecewiseAffine : chart.IsFinitePL
  link : ∀ x : (K.barycentricDualBlock {p}).space,
    (x : E) ∈ ((K.barycentricDualBlock {p}).link p).space ↔
      (chart x : V3) ∈ frontier body
  boundary : ∀ x : (K.barycentricDualBlock {p}).space,
    height (chart x : V3) = 0 ↔ (x : E) ∈ (L.barycentricDualBlock {p}).space



theorem exists_boundary_vertex_half_ball [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] (hLK : L ≤ K) {R : Set X}
    (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (HB : L.space ≃ₜ frontier R)
    (hHB : ∀ z : L.space, (HB z : X) = (g z : X))
    {p : E} (hp : p ∈ L.vertices)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    Nonempty (BoundaryVertexHalfBall K L p) := by
  obtain ⟨C, A, v, G, hv, hC, hcv, hC0, hpoly, hball, hG, hGb, hG0⟩ :=
    PoincareConjecture.M76.exists_original_boundary_dual_half_ball K L hLK H g hg HB hHB
      hp B hsource hface hregion
  exact ⟨⟨C, A, v, G, hv, hC, hcv, hC0, hpoly, hball, hG, hGb, hG0⟩⟩

end Geometry.SimplicialComplex
