import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.Tangential
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateLifts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.exists_hamiltonZero_second_phase_adjustment
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (W : C(X0, V3))
    (hW : ∀ i, LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target)
    (hWphase : ∀ x, W x 1 = 0)
    {B : Set X0} (hWzero : ∀ x ∈ B, W x = 0) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (∀ x, hamiltonZeroAmbientMap psi x =
        hamiltonZeroTargetVectorTranslation (W x, hamiltonZeroAmbientMap phi x)) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) B,
        ∀ t x, (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x := by
  let G : C(unitInterval × X0, X0) :=
    ⟨fun z => hamiltonZeroTargetVectorTranslation
      ((z.1 : ℝ) • W z.2, hamiltonZeroAmbientMap phi z.2),
      hamiltonZeroTargetVectorTranslation.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).smul
          (W.continuous.comp continuous_snd)).prodMk
          ((hamiltonZeroAmbientMap phi).continuous.comp continuous_snd))⟩
  have hGzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := by
    change hamiltonZeroTargetVectorTranslation ((0 : ℝ) • W x, _) = _
    rw [zero_smul, hamiltonZeroTargetVectorTranslation_zero]
  have hGone (x : X0) : G (1, x) =
      hamiltonZeroTargetVectorTranslation (W x, hamiltonZeroAmbientMap phi x) := by
    change hamiltonZeroTargetVectorTranslation ((1 : ℝ) • W x, _) = _
    rw [one_smul]
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap g
  have hg (x : X0) : hamiltonZeroAmbientMap psi x = G (1, x) := by
    rw [hamiltonZeroAmbientMap_handle]
    rfl
  have hphase (t : unitInterval) (x : X0) :
      (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x := by
    change (Q0 (hamiltonZeroTargetVectorTranslation
      ((t : ℝ) • W x, hamiltonZeroAmbientMap phi x))).1.2 = _
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    simp only [Pi.smul_apply, smul_eq_mul, hWphase, mul_zero, AddCircle.coe_zero, add_zero]
    exact (hamiltonZeroSecondCircleMap_ambient phi x).symm
  refine ⟨psi, ?_, ⟨hamiltonZeroHandleHomotopy phi G hGzero⟩,
    ⟨F.trans (hamiltonZeroHandleHomotopy phi G hGzero)⟩, ?_,
    fun x => (hg x).trans (hGone x), ?_⟩
  · rw [hamiltonZeroHandleMap_domain]
    have heq : g = ⟨fun x => hamiltonZeroTargetVectorTranslation
        (W x, hamiltonZeroAmbientMap phi x),
      hamiltonZeroTargetVectorTranslation.continuous.comp
        (W.continuous.prodMk (hamiltonZeroAmbientMap phi).continuous)⟩ :=
      ContinuousMap.ext hGone
    rw [heq]
    exact chartwisePL_hamiltonZero_vector_translation hd hphi W hW
  · apply ContinuousMap.ext
    intro x
    rw [hamiltonZeroSecondCircleMap_ambient, hg]
    exact hphase 1 x
  · refine ⟨{
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hGzero
      map_one_left := fun x => (hg x).symm
      prop' := ?_ }, hphase⟩
    intro t x hx
    change hamiltonZeroTargetVectorTranslation ((t : ℝ) • W x, _) = _
    rw [hWzero x hx, smul_zero, hamiltonZeroTargetVectorTranslation_zero]

end PoincareConjecture.M76
