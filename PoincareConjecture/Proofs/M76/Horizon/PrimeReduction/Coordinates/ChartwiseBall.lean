import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleNormalCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem chartwisePLBall_of_finitePLBallPair_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (Q : OpenPartialHomeomorph X V3)
    (hcover : ∀ y ∈ Q.source, ∃ i, y ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (c : E ≃L[ℝ] V3) {D bd : Set V3}
    (hD : IsFinitePLBallPair E D bd) (hDQ : D ⊆ Q.target) :
    Nonempty (ChartwisePLBall e (Q.symm '' D) (Q.symm '' bd)) := by
  obtain ⟨b, hb, hboundary⟩ := hD.exists_cube_chart c
  obtain ⟨f, hf, hfeq⟩ := hb.symm
  let q : D ≃ₜ Q.symm '' D :=
    Q.symm.homeomorphOfImageSubsetSource hDQ rfl
  have hftarget : MapsTo f (closedBall (0 : V3) 1) Q.target := by
    intro x hx
    rw [← hfeq ⟨x, hx⟩]
    exact hDQ (b.symm ⟨x, hx⟩).property
  have hPL : PolyhedralPLInCharts e (Q.symm ∘ f) (closedBall (0 : V3) 1) := by
    have hfcopy := hf
    obtain ⟨K, hK, hKs, _⟩ := hfcopy
    rw [← hKs]
    exact polyhedralPLInCharts_of_compatible_inverse e Q hcover hQ K hK
      (hKs.symm ▸ hf) (hKs.symm ▸ hftarget)
  have hboundaryImage (y : D) : Q.symm y ∈ Q.symm '' bd ↔ (y : V3) ∈ bd := by
    constructor
    · rintro ⟨x, hx, heq⟩
      exact Q.symm.injOn (hDQ (hD.1 hx)) (hDQ y.property) heq ▸ hx
    · exact fun hy => ⟨y, hy, rfl⟩
  refine ⟨{
    boundary_subset := image_mono hD.1
    parametrization := b.symm.trans q
    map := Q.symm ∘ f
    map_eq := ?_
    piecewiseAffine := hPL
    boundary_eq := ?_
  }⟩
  · intro x
    change Q.symm (f x) = Q.symm (b.symm x)
    exact congrArg Q.symm (hfeq x).symm
  · intro x
    change Q.symm (b.symm x) ∈ Q.symm '' bd ↔ (x : V3) ∈ sphere (0 : V3) 1
    rw [hboundaryImage, hboundary, b.apply_symm_apply, frontier_closedBall _ one_ne_zero]

end PoincareConjecture.M76
