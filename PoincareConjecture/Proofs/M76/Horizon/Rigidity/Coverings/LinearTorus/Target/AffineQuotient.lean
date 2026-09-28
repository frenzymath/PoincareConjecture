import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension



set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {ι κ β : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)}

local notation "Vcoord" => ((ι ⊕ κ) → ℝ)
local notation "X" => LatticeHandleAmbient ι κ L
local notation "pi" => latticeCoordinateProjection ι κ L

theorem StandardLatticeHandleAtlas.polyhedralPL_postcomp_quotient_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : β → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (T : C(X, X)) (B : Vcoord →ᴬ[ℝ] Vcoord) (hB : ∀ v, T (pi v) = pi (B v))
    {Y : E → X} {S : Set E} (hY : PolyhedralPLInCharts d Y S) :
    PolyhedralPLInCharts d (T ∘ Y) S := by
  classical
  refine ⟨T.continuous.comp_continuousOn hY.continuousOn, ?_⟩
  intro x
  obtain ⟨i, J, V, hJ, hJS, hV, hxV, hVJ, hYi, hcoords⟩ := hY.coordinates x
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let split := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ
    (fun _ => ℝ)).toContinuousAffineEquiv
  let a := a0.trans split.symm
  have ha (z : Fin 3 → ℝ) (hz : z ∈ (d i).target) : pi (a z) = (d i).symm z := by
    rw [ha0 z hz]
    rfl
  let v : E → ((ι ⊕ κ) → ℝ) := a ∘ (d i) ∘ Y
  have hv : FinitePiecewiseAffineOn v J.space := by
    simpa only [v, Function.comp_def, ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      hcoords.postcomp a.toContinuousAffineMap
  have hprojection (y : E) (hy : y ∈ J.space) : pi (v y) = Y y := by
    change pi (a (d i (Y y))) = Y y
    rw [ha _ ((d i).map_source (hYi hy)), (d i).left_inv (hYi hy)]
  have hlocal : PolyhedralPLInCharts d (T ∘ Y) J.space := by
    apply (hd.polyhedralPL_projection (hv.postcomp B)).congr
    intro y hy
    change pi (B (v y)) = T (Y y)
    rw [← hB, hprojection y hy]
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
