import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicModelOrder
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false
open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)

theorem exists_original_boundary_circle_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] {S : Set E}
    (gamma : sphere (0 : V2) 1 ≃ₜ S) (hgamma : gamma.IsFinitePL)
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (hLs : L.space = S) :
    (∀ s ∈ L.faces, s.card ≤ 2) ∧
      ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
        P.HasSimplicialEdges ∧ range P = L.vertices ∧ P.boundary ℝ = L.space ∧
        (∀ s : Finset E, s ∈ L.faces ↔ s.Nonempty ∧
          ∃ j : Fin (n + 3), s ⊆ {P j, P (finRotate (n + 3) j)}) ∧
        ∀ s : Finset E, (s ∈ L.faces ∧ s.card = 2) ↔
          ∃ j : Fin (n + 3), s = {P j, P (finRotate (n + 3) j)} := by
  classical
  have hball : IsFinitePLBallPair (ℝ × ℝ) (closedBall (0 : V2) 1) (sphere (0 : V2) 1) :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨n, Q, hQi, hQ, hQs⟩ := hball.exists_polygon_boundary
  obtain ⟨g, hg, hgv⟩ := hgamma
  have hgi : InjOn g (sphere (0 : V2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (gamma.injective (Subtype.ext
      ((hgv ⟨x, hx⟩).trans (hxy.trans (hgv ⟨y, hy⟩).symm))))
  have himage : g '' sphere (0 : V2) 1 = S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hgv ⟨x, hx⟩) ▸ (gamma ⟨x, hx⟩).property
    · intro hy
      let x := gamma.symm ⟨y, hy⟩
      exact ⟨x, x.property, (hgv x).symm.trans
        (congrArg Subtype.val (gamma.apply_symm_apply ⟨y, hy⟩))⟩
  obtain ⟨m, P, hPi, hP, hPs⟩ := Q.exists_polygon_finitePL_image
    hQ hQi hg hQs.subset (hgi.mono hQs.subset)
  have hPL : P.boundary ℝ = L.space := by rw [hPs, hQs, himage, hLs]
  have hconn : IsConnected L.space := by
    rw [hLs, ← himage]
    exact (isConnected_sphere (by simp) (0 : V2) zero_le_one).image g hg.continuousOn
  exact ⟨fun s hs => L.face_card_le_two_of_polygon_carrier P hPL.symm.subset hs,
    L.exists_exact_cyclic_polygon_of_polygon_carrier hL hconn P hP hPi hPL⟩

end PoincareConjecture.M76.Dehn
