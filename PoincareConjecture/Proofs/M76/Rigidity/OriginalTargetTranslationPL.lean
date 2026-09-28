import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetTranslation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.StandardTargetTranslationPL
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V0" => ((Fin 0 ⊕ Fin 3) → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "pi" => latticeCoordinateProjection (Fin 0) (Fin 3) L0

theorem StandardLatticeHandleAtlas.polyhedralPL_hamiltonZeroTargetTranslation
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {Y : E → X0} {w : E → ℝ} {S : Set E}
    (hY : PolyhedralPLInCharts d Y S) (hw : FinitePiecewiseAffineOn w S) :
    PolyhedralPLInCharts d (fun x => hamiltonZeroTargetTranslation (w x, Y x)) S := by
  classical
  let n : ℝ →L[ℝ] V0 := ContinuousLinearMap.pi fun j =>
    if j = Sum.inr (2 : Fin 3) then ContinuousLinearMap.id ℝ ℝ else 0
  have htranslation (u : ℝ) (v : V0) :
      hamiltonZeroTargetTranslation (u, pi v) = pi (v + n u) := by
    change hamiltonZeroTargetTranslation
      (u, ((fun i => v (Sum.inl i)), QuotientAddGroup.mk (fun j => v (Sum.inr j)))) = _
    rw [hamiltonZeroTargetTranslation_mk]
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · apply congrArg QuotientAddGroup.mk
      funext j
      fin_cases j <;> simp [n]
  refine ⟨hamiltonZeroTargetTranslation.continuous.comp_continuousOn
    (hw.continuousOn.prodMk hY.continuousOn), ?_⟩
  intro x
  obtain ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, hYi, hcoords⟩ := hY.coordinates x
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let split := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
    (fun _ => ℝ)).toContinuousAffineEquiv
  let a := a0.trans split.symm
  have ha (z : V3) (hz : z ∈ (d i).target) : pi (a z) = (d i).symm z := by
    rw [ha0 z hz]
    rfl
  let v : E → V0 := a ∘ (d i) ∘ Y
  have hv : FinitePiecewiseAffineOn v J.space := by
    simpa only [v, Function.comp_def, ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      hcoords.postcomp a.toContinuousAffineMap
  have hprojection (y : E) (hy : y ∈ J.space) : pi (v y) = Y y := by
    change pi (a (d i (Y y))) = Y y
    rw [ha _ ((d i).map_source (hYi hy)), (d i).left_inv (hYi hy)]
  have hlocal : PolyhedralPLInCharts d
      (fun y => hamiltonZeroTargetTranslation (w y, Y y)) J.space := by
    apply (hd.polyhedralPL_projection_add_linear hv (hw.restrict J hJ hJS) n).congr
    intro y hy
    change pi (v y + n (w y)) = hamiltonZeroTargetTranslation (w y, Y y)
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

end PoincareConjecture.M76
