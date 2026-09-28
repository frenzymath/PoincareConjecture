import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroHandleStraightening
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonTheoremOne
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "W" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "Y" => ((Set.singleton hamiltonZeroHandlePuncture)ᶜ : Set W)
local notation "V3" => (Fin 3 → ℝ)
local notation "V" => ((Fin 0 ⊕ Fin 3) → ℝ)
local notation "R" => latticeHandleDomain (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

private noncomputable def zeroSumCoordinates : V ≃ᴬ[ℝ] V3 :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin 0 ⊕ Fin 3 => ℝ)
    (Equiv.emptySum (Fin 0) (Fin 3))).toAffineEquiv.toContinuousAffineEquiv

private theorem zeroSumCoordinates_apply (x : V) (j : Fin 3) :
    zeroSumCoordinates x j = x (Sum.inr j) := rfl

private theorem zeroSumCoordinates_norm (x : V) : ‖zeroSumCoordinates x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    exact fun j => norm_le_pi_norm x (Sum.inr j)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (zeroSumCoordinates x))).mpr
    intro j
    cases j with
    | inl j => exact isEmptyElim j
    | inr j => exact norm_le_pi_norm (zeroSumCoordinates x) j

private def zeroProductLinear : CubeShell.Ambient ≃ₗ[ℝ] V3 where
  toFun x := fun j => CubeShell.coordinate j x
  invFun := CubeShell.vector
  left_inv := CubeShell.vector_coordinate
  right_inv x := funext (CubeShell.coordinate_vector x)
  map_add' x y := by ext j; exact map_add (CubeShell.coordinate j) x y
  map_smul' r x := by ext j; exact map_smul (CubeShell.coordinate j) r x

private noncomputable def zeroProductCoordinates : CubeShell.Ambient ≃ᴬ[ℝ] V3 :=
  zeroProductLinear.toContinuousLinearEquiv.toContinuousAffineEquiv

theorem hasHamiltonChartHandleStraightening_zero_of_named_inputs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    (wall : ∀ e : Y → OpenPartialHomeomorph Y V3, HasWallCompactCore e)
    (brown : HasBrownLocallyFlatSphereBalls)
    (prime : ∀ charts : Set (OpenPartialHomeomorph W V3),
      HasHamiltonProtectedIrreducibleReplacement (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
        (fun c : charts => (c : OpenPartialHomeomorph W V3)))
    (approximation : ∀ (charts : Set (OpenPartialHomeomorph W V3))
      (d : ((Fin 0 → ℝ) × V3) → OpenPartialHomeomorph W V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph W V3)) d R)
    (rigidity : ∀ (charts : Set (OpenPartialHomeomorph W V3))
      (d : ((Fin 0 → ℝ) × V3) → OpenPartialHomeomorph W V3),
      HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
        (fun c : charts => (c : OpenPartialHomeomorph W V3)) d) :
    HasHamiltonChartHandleStraightening E ∅ := by
  intro e hsource N _ _ _
  have hcyl : coordinateCylinder (∅ : Finset (Fin 3)) = univ := by
    ext x
    simp [coordinateCylinder]
  have hesource : e.source = univ := by
    apply eq_univ_of_forall
    intro x
    exact hsource (hcyl.symm ▸ mem_univ x)
  let a := zeroSumCoordinates
  let b : E ≃ᴬ[ℝ] V3 :=
    (ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)).toContinuousAffineEquiv
  let h := (zeroProductCoordinates.toHomeomorph.transOpenPartialHomeomorph e).transHomeomorph
    b.toHomeomorph
  have hhs : h.source = univ := by
    ext x
    change zeroProductCoordinates x ∈ e.source ↔ x ∈ (univ : Set CubeShell.Ambient)
    rw [hesource]
    simp only [mem_univ]
  obtain ⟨B, hBPL, ⟨HB⟩⟩ :=
    exists_hamilton_zero_handle_straightening h hhs wall brown prime approximation rigidity
  have hactual (x : V) :
      h (CubeShell.vector (fun j => x (Sum.inr j))) = b (e (a x)) := by
    change b (e (zeroProductCoordinates (CubeShell.vector (fun j => x (Sum.inr j))))) = _
    congr 2
    ext j
    exact CubeShell.coordinate_vector _ j
  have htarget : FinitePiecewiseAffineOn (fun x => e (a (B x))) (closedBall (0 : V) 1) := by
    apply (hBPL.postcomp b.symm.toContinuousAffineMap).congr
    intro x _
    change b.symm (h (CubeShell.vector (fun j => (B x) (Sum.inr j)))) = e (a (B x))
    rw [hactual, b.symm_apply_apply]
  let C : V3 ≃ₜ V3 := a.symm.toHomeomorph.trans (B.trans a.toHomeomorph)
  have hnorm (x : V3) : ‖a.symm x‖ = ‖x‖ := by
    have hh : ‖a (a.symm x)‖ = ‖a.symm x‖ := zeroSumCoordinates_norm (a.symm x)
    rw [a.apply_symm_apply] at hh
    exact hh.symm
  have hball : a '' closedBall (0 : V) 1 = closedBall (0 : V3) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply mem_closedBall_zero_iff.mpr
      rw [show ‖a y‖ = ‖y‖ from zeroSumCoordinates_norm y]
      exact mem_closedBall_zero_iff.mp hy
    · intro hx
      exact ⟨a.symm x, by simpa only [mem_closedBall_zero_iff, hnorm] using hx,
        a.apply_symm_apply x⟩
  have hCPL : FinitePiecewiseAffineOn (e ∘ C) (closedBall (0 : V3) 1) := by
    have hh := htarget.precomp_affineEquiv a.symm
    change FinitePiecewiseAffineOn (e ∘ C) (a '' closedBall (0 : V) 1) at hh
    rwa [hball] at hh
  have hCout (x : V3) (hx : 2 ≤ ‖x‖) : C x = x := by
    have hfix := (HB.prop 1).2.1 (a.symm x) (by rwa [hnorm])
    change HB (1, a.symm x) = a.symm x at hfix
    rw [HB.apply_one] at hfix
    change B (a.symm x) = a.symm x at hfix
    change a (B (a.symm x)) = x
    rw [hfix, a.apply_symm_apply]
  have hstar : StarConvex ℝ (0 : V3) (coordinateCylinder (∅ : Finset (Fin 3))) :=
    (convex_coordinateCylinder ∅).starConvex (by intro j hj; simp at hj)
  exact ⟨C, hCPL, ⟨C.relativeSupportedAlexanderHomotopy (by norm_num) hCout hstar
    (fun x hx => False.elim (hx (hcyl.symm ▸ mem_univ x)))⟩⟩

end PoincareConjecture.M76
