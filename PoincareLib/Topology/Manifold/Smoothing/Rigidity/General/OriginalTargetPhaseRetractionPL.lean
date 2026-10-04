import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.OriginalTargetPhaseRetraction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.OriginalTargetTranslationPL

/-!
# Original-atlas PL of the constructed target phase retraction

Each complete standard inverse-chart patch supplies its own affine lift.
Replacing the last real coordinate by a constant and taking the original
quotient proves PL of the actual phase retraction on that whole patch.
See Waldhausen1968, p.60, and rigidity057, section2.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V0" => ((Fin 0 ⊕ Fin 3) → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "pi" => latticeCoordinateProjection (Fin 0) (Fin 3) L0

/-- The literal phase retraction of a map PL in the original standard
target atlas is PL on the same whole carrier. Its local affine lifts
and complete coordinate replacement are constructed internally.
See rigidity057, section2. -/
theorem StandardLatticeHandleAtlas.polyhedralPL_hamiltonZeroTargetPhaseRetraction
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (theta : ℝ) {Y : E → X0} {S : Set E}
    (hY : PolyhedralPLInCharts d Y S) :
    PolyhedralPLInCharts d (hamiltonZeroTargetPhaseRetraction theta ∘ Y) S := by
  classical
  let m : V0 →L[ℝ] V0 := ContinuousLinearMap.pi fun j =>
    if j = Sum.inr (2 : Fin 3) then 0 else ContinuousLinearMap.proj j
  let b : V0 := fun j => if j = Sum.inr (2 : Fin 3) then theta else 0
  let a : V0 →ᴬ[ℝ] V0 := m.toContinuousAffineMap + ContinuousAffineMap.const ℝ V0 b
  have hretract (v : V0) : hamiltonZeroTargetPhaseRetraction theta (pi v) = pi (a v) := by
    change hamiltonZeroTargetPhaseRetraction theta
      ((fun i => v (Sum.inl i)), QuotientAddGroup.mk (fun j => v (Sum.inr j))) = _
    rw [hamiltonZeroTargetPhaseRetraction_mk]
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply congrArg QuotientAddGroup.mk
      funext j
      fin_cases j <;> simp [a, b, m]
  refine ⟨(hamiltonZeroTargetPhaseRetraction theta).continuous.comp_continuousOn
    hY.continuousOn, ?_⟩
  intro x
  obtain ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, hYi, hcoords⟩ := hY.coordinates x
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let split := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
    (fun _ => ℝ)).toContinuousAffineEquiv
  let lift := a0.trans split.symm
  have hlift (z : V3) (hz : z ∈ (d i).target) : pi (lift z) = (d i).symm z := by
    rw [ha0 z hz]
    rfl
  let v : E → V0 := lift ∘ (d i) ∘ Y
  have hv : FinitePiecewiseAffineOn v J.space := by
    simpa only [v, Function.comp_def, ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      hcoords.postcomp lift.toContinuousAffineMap
  have hprojection (y : E) (hy : y ∈ J.space) : pi (v y) = Y y := by
    change pi (lift (d i (Y y))) = Y y
    rw [hlift _ ((d i).map_source (hYi hy)), (d i).left_inv (hYi hy)]
  have hlocal : PolyhedralPLInCharts d
      (hamiltonZeroTargetPhaseRetraction theta ∘ Y) J.space := by
    apply (hd.polyhedralPL_projection (hv.postcomp a)).congr
    intro y hy
    change pi (a (v y)) = hamiltonZeroTargetPhaseRetraction theta (Y y)
    rw [← hretract, hprojection y hy]
  have hxJ : (x : E) ∈ J.space := hVJ ⟨x, hxV, rfl⟩
  obtain ⟨j, N, W, hN, hNJ, hW, hxW, hWN, htarget, hformula⟩ :=
    hlocal.coordinates ⟨x, hxJ⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  have hxO : (x : E) ∈ O := by
    change (⟨x, hxJ⟩ : J.space) ∈ Subtype.val ⁻¹' O
    rw [hOW]
    exact hxW
  refine ⟨j, N, V ∩ (Subtype.val : S → E) ⁻¹' O,
    hN, hNJ.trans hJS, hV.inter (hO.preimage continuous_subtype_val),
    ⟨hxV, hxO⟩, ?_, htarget, hformula⟩
  rintro y ⟨z, hz, rfl⟩
  have hzJ : (z : E) ∈ J.space := hVJ ⟨z, hz.1, rfl⟩
  have hzW : (⟨z, hzJ⟩ : J.space) ∈ W := by
    rw [← hOW]
    exact hz.2
  exact hWN ⟨⟨z, hzJ⟩, hzW, rfl⟩

end PoincareMT.M76
