import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.PeriodicCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Polyhedra.Mathlib.LocallyInjectivePLLift



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.finitePiecewiseAffineOn_periodic_lift
    {E Z V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    (J : SimplicialComplex ℝ Z) (hJ : J.faces.Finite)
    {r : Z → P2} (hr : ContinuousOn r J.space)
    (hf : PolyhedralPLInCharts e
      (fun z => (h (((r z).1 : AddCircle p), ((r z).2 : AddCircle p)) : X)) J.space) :
    FinitePiecewiseAffineOn r J.space := by
  have hp : 0 < p := Fact.out
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp
    ((J.isCompact_space_of_finite hJ).image_of_continuousOn hr).isBounded
  let d := |B| + 1
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨P, hP, hPs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (show -d < d by linarith)).prod
      (isFinitePLBallPair_Icc (show -d < d by linarith))
  have hrP : MapsTo r J.space P.space := by
    intro z hz
    rw [hPs]
    have hnorm : ‖r z‖ ≤ d := (hB _ ⟨z, hz, rfl⟩).trans
      ((le_abs_self B).trans (by dsimp [d]; linarith))
    exact ⟨abs_le.mp ((show |(r z).1| ≤ ‖r z‖ by
        simpa only [Real.norm_eq_abs] using norm_fst_le (r z)).trans hnorm),
      abs_le.mp ((show |(r z).2| ≤ ‖r z‖ by
        simpa only [Real.norm_eq_abs] using norm_snd_le (r z)).trans hnorm)⟩
  let f (z : P2) : X := h ((z.1 : AddCircle p), (z.2 : AddCircle p))
  have hfP : PolyhedralPLInCharts e f P.space :=
    M.polyhedralPL_periodic_comp H F hF hFval h hvalue P hP
      ((P.affineOnFaces_affine (ContinuousAffineMap.id ℝ P2)).finitePiecewiseAffineOn hP)
  have hlocal : IsLocallyInjective (fun z : P.space => f z) := by
    intro z
    let Q := (AddCircle.openPartialHomeomorphCoe p (z.1.1 - p / 2)).prod
      (AddCircle.openPartialHomeomorphCoe p (z.1.2 - p / 2))
    have hzQ : (z : P2) ∈ Q.source := by
      change (z.1.1 ∈ Ioo (z.1.1 - p / 2) (z.1.1 - p / 2 + p)) ∧
        (z.1.2 ∈ Ioo (z.1.2 - p / 2) (z.1.2 - p / 2 + p))
      constructor <;> constructor <;> linarith
    refine ⟨(Subtype.val : P.space → P2) ⁻¹' Q.source,
      Q.open_source.preimage continuous_subtype_val, hzQ, ?_⟩
    intro x hx y hy heq
    apply Subtype.ext
    apply Q.injOn hx hy
    exact h.injective (Subtype.ext heq)
  exact hfP.finitePiecewiseAffineOn_lift_of_locallyInjective hcompat P hP hlocal
    J hJ hr hrP hf

end PoincareConjecture.M76.PeriodicSquare
