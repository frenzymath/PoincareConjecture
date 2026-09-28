import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.SourcePhase
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.StandardTargetTranslationPL
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

noncomputable def targetTranslation : C(ℝ × X, X) where
  toFun z := (z.2.1, z.2.2 + QuotientAddGroup.mk ![0, z.1])
  continuous_toFun := by fun_prop

noncomputable def handleTranslation : C(ℝ × H, H) where
  toFun z := (z.2.1, z.2.2 + QuotientAddGroup.mk ![0, z.1])
  continuous_toFun := by fun_prop

theorem targetTranslation_zero (x : X) : targetTranslation (0, x) = x := by
  change (x.1, x.2 + QuotientAddGroup.mk ![0, (0 : ℝ)]) = x
  have h0 : (![0, (0 : ℝ)] : V2) = 0 := by ext i; fin_cases i <;> rfl
  simp [h0]

theorem handleTranslation_zero (x : H) : handleTranslation (0, x) = x := by
  change (x.1, x.2 + QuotientAddGroup.mk ![0, (0 : ℝ)]) = x
  have h0 : (![0, (0 : ℝ)] : V2) = 0 := by ext i; fin_cases i <;> rfl
  simp [h0]

theorem targetTranslation_mk (t : ℝ) (x : V1) (v : V2) :
    targetTranslation (t, (x, QuotientAddGroup.mk v)) =
      (x, QuotientAddGroup.mk (v + ![0, t])) := by
  change (x, QuotientAddGroup.mk v + QuotientAddGroup.mk ![0, t]) = _
  rw [← QuotientAddGroup.mk_add]

theorem handleTranslation_coordinates (t : ℝ) (x : H) :
    hamiltonOneHierarchyCoordinates (handleTranslation (t, x)) =
      ((hamiltonOneHierarchyCoordinates x).1,
        (hamiltonOneHierarchyCoordinates x).2 + (t : C)) := by
  rcases x with ⟨x, v⟩
  induction v using QuotientAddGroup.induction_on with | «H» v =>
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    change hamiltonOneHierarchyCoordinates
      (x, QuotientAddGroup.mk v + QuotientAddGroup.mk ![0, t]) = _
    rw [← QuotientAddGroup.mk_add]
    have hsum : v + ![0, t] = ![v 0, v 1 + t] := by ext i; fin_cases i <;> simp
    rw [hsum, hamiltonOneHierarchyCoordinates_mk, hv, hamiltonOneHierarchyCoordinates_mk]
    simp

theorem handleTranslation_domain (t : ℝ) (x : H) :
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
      (handleTranslation (t, x)) : X) =
        targetTranslation (t, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X)) := rfl

theorem polyhedralPL_targetTranslation
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {Y : E → X} {w : E → ℝ} {S : Set E}
    (hY : PolyhedralPLInCharts d Y S) (hw : FinitePiecewiseAffineOn w S) :
    PolyhedralPLInCharts d (fun x => targetTranslation (w x, Y x)) S := by
  classical
  let V := (Fin 1 ⊕ Fin 2) → ℝ
  let pi := latticeCoordinateProjection (Fin 1) (Fin 2) L
  let n : ℝ →L[ℝ] V := ContinuousLinearMap.pi fun j =>
    if j = Sum.inr (1 : Fin 2) then ContinuousLinearMap.id ℝ ℝ else 0
  have htranslation (u : ℝ) (v : V) : targetTranslation (u, pi v) = pi (v + n u) := by
    rw [show pi v = ((fun i => v (Sum.inl i)),
      QuotientAddGroup.mk (fun j => v (Sum.inr j))) from rfl, targetTranslation_mk]
    apply Prod.ext
    · funext i
      change v (Sum.inl i) = v (Sum.inl i) + n u (Sum.inl i)
      simp [n, V, ContinuousLinearMap.pi_apply]
    · apply congrArg QuotientAddGroup.mk
      funext j
      change v (Sum.inr j) + (![0, u] : V2) j = v (Sum.inr j) + n u (Sum.inr j)
      fin_cases j <;> simp [n, V, ContinuousLinearMap.pi_apply]
  refine ⟨targetTranslation.continuous.comp_continuousOn
    (hw.continuousOn.prodMk hY.continuousOn), ?_⟩
  intro x
  obtain ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, hYi, hcoords⟩ := hY.coordinates x
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let split := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin 2)
    (fun _ => ℝ)).toContinuousAffineEquiv
  let a := a0.trans split.symm
  have ha (z : V3) (hz : z ∈ (d i).target) : pi (a z) = (d i).symm z := by
    rw [ha0 z hz]
    rfl
  let v := a ∘ (d i) ∘ Y
  have hv : FinitePiecewiseAffineOn v J.space := by
    simpa only [v, Function.comp_def, ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      hcoords.postcomp a.toContinuousAffineMap
  have hprojection (y : E) (hy : y ∈ J.space) : pi (v y) = Y y := by
    change pi (a (d i (Y y))) = Y y
    rw [ha _ ((d i).map_source (hYi hy)), (d i).left_inv (hYi hy)]
  have hlocal : PolyhedralPLInCharts d (fun y => targetTranslation (w y, Y y)) J.space := by
    apply (hd.polyhedralPL_projection_add_linear hv (hw.restrict J hJ hJS) n).congr
    intro y hy
    change pi (v y + n (w y)) = targetTranslation (w y, Y y)
    rw [← htranslation, hprojection y hy]
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

end PoincareConjecture.M76.HamiltonIntervalTorus
