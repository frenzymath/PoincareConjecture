import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.FromPLTorus



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "V3" => (Fin 3 → ℝ)

theorem SourceSquareMap.exists_original_PL_parameter
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ z : K.space, F z = (H z : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z)) :
    ∃ v : ℝ × ℝ → X, PolyhedralPLInCharts e v (squareCarrier p) ∧
      ∀ z : Square p, v (z.1, z.2) = (h (projection p z) : X) := by
  obtain ⟨U, hU, hUv⟩ := M.finite_piecewise_affine
  have hmap : MapsTo U (squareCarrier p) K.space := by
    intro z hz
    let z' : Square p := (⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩)
    have hh := hUv z'
    change U z = (M.map z' : E) at hh
    rw [hh]
    exact (M.map z').property
  have hp : 0 < p := Fact.out
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc hp).prod (isFinitePLBallPair_Icc hp)
  have hv : PolyhedralPLInCharts e (F ∘ U) L.space :=
    hF.comp_finitePiecewiseAffineOn L hL (hLs.symm ▸ hU) (hLs.symm ▸ hmap)
  refine ⟨F ∘ U, ?_, ?_⟩
  · simpa only [hLs, squareCarrier] using hv
  intro z
  change F (U (z.1, z.2)) = (h (projection p z) : X)
  rw [hUv, hFval, ← hvalue]

end PoincareConjecture.M76.PeriodicSquare
