import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.OriginalScalarTranslationPL

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.exists_hamiltonZero_scalar_homotopy {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (w : C(X0, ℝ))
    (hw : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    {U : Set X0} (hzero : ∀ x, x ∉ U → w x = 0) :
    ∃ G : C(unitInterval × X0, X0),
      (∀ (t : unitInterval) (x : X0), G (t, x) =
        hamiltonZeroTargetTranslation ((t : ℝ) * w x, hamiltonZeroAmbientMap phi x)) ∧
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ U → G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ x, (Q0 (G (1, x))).2 = hamiltonZeroCircleMap phi x + (w x : C0)) ∧
      let g : C(X0, X0) := ⟨fun x => G (1, x),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      ChartwisePLMap e d
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap g)) ∧
        Nonempty (phi.HomotopyRel (hamiltonZeroHandleMap g) B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel (hamiltonZeroHandleMap g) B0) := by
  let G : C(unitInterval × X0, X0) :=
    ⟨fun z => hamiltonZeroTargetTranslation
      ((z.1 : ℝ) * w z.2, hamiltonZeroAmbientMap phi z.2),
      hamiltonZeroTargetTranslation.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).mul (w.continuous.comp continuous_snd)).prodMk
          ((hamiltonZeroAmbientMap phi).continuous.comp continuous_snd))⟩
  have hGzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := by
    change hamiltonZeroTargetTranslation ((0 : ℝ) * w x, hamiltonZeroAmbientMap phi x) = _
    rw [zero_mul, hamiltonZeroTargetTranslation_zero]
  have hGone (x : X0) : G (1, x) =
      hamiltonZeroTargetTranslation (w x, hamiltonZeroAmbientMap phi x) := by
    change hamiltonZeroTargetTranslation ((1 : ℝ) * w x, hamiltonZeroAmbientMap phi x) = _
    rw [one_mul]
  refine ⟨G, fun _ _ => rfl, hGzero, ?_, ?_, ?_⟩
  · intro t x hx
    change hamiltonZeroTargetTranslation ((t : ℝ) * w x, hamiltonZeroAmbientMap phi x) = _
    rw [hzero x hx, mul_zero, hamiltonZeroTargetTranslation_zero]
  · intro x
    rw [hGone, hamiltonZeroTargetTranslation_coordinates]
    rfl
  · refine ⟨?_, ⟨hamiltonZeroHandleHomotopy phi G hGzero⟩,
      ⟨F.trans (hamiltonZeroHandleHomotopy phi G hGzero)⟩⟩
    rw [hamiltonZeroHandleMap_domain]
    let g : C(X0, X0) := ⟨fun x => hamiltonZeroTargetTranslation (w x, hamiltonZeroAmbientMap phi x),
      hamiltonZeroTargetTranslation.continuous.comp
        (w.continuous.prodMk (hamiltonZeroAmbientMap phi).continuous)⟩
    have hgeq : (⟨fun x => G (1, x),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(X0, X0)) = g :=
      ContinuousMap.ext hGone
    rw [hgeq]
    exact chartwisePL_hamiltonZero_scalar_translation hd hphi w hw

end PoincareConjecture.M76
