import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Translations.OriginalVector
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalScalarHomotopy

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

theorem ChartwisePLMap.exists_hamiltonZero_tangential_homotopy {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (w : C(X0, V3))
    (hw : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    (hnormal : ∀ x, w x 2 = 0)
    {U : Set X0} (hzero : ∀ x, x ∉ U → w x = 0) :
    ∃ G : C(unitInterval × X0, X0),
      (∀ (t : unitInterval) (x : X0), G (t, x) =
        hamiltonZeroTargetVectorTranslation ((t : ℝ) • w x, hamiltonZeroAmbientMap phi x)) ∧
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ U → G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x) ∧
      (∀ x, (Q0 (G (1, x))).1 =
        ((Q0 (hamiltonZeroAmbientMap phi x)).1.1 + (w x 0 : C0),
          (Q0 (hamiltonZeroAmbientMap phi x)).1.2 + (w x 1 : C0))) ∧
      let g : C(X0, X0) := ⟨fun x => G (1, x),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      ChartwisePLMap e d
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap g)) ∧
        Nonempty (phi.HomotopyRel (hamiltonZeroHandleMap g) B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel (hamiltonZeroHandleMap g) B0) ∧
        hamiltonZeroCircleMap (hamiltonZeroHandleMap g) = hamiltonZeroCircleMap phi := by
  let G : C(unitInterval × X0, X0) :=
    ⟨fun z => hamiltonZeroTargetVectorTranslation
      ((z.1 : ℝ) • w z.2, hamiltonZeroAmbientMap phi z.2),
      hamiltonZeroTargetVectorTranslation.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).smul
          (w.continuous.comp continuous_snd)).prodMk
            ((hamiltonZeroAmbientMap phi).continuous.comp continuous_snd))⟩
  have hGzero (x : X0) : G (0, x) = hamiltonZeroAmbientMap phi x := by
    change hamiltonZeroTargetVectorTranslation ((0 : ℝ) • w x, _) = _
    rw [zero_smul, hamiltonZeroTargetVectorTranslation_zero]
  have hGone (x : X0) : G (1, x) =
      hamiltonZeroTargetVectorTranslation (w x, hamiltonZeroAmbientMap phi x) := by
    change hamiltonZeroTargetVectorTranslation ((1 : ℝ) • w x, _) = _
    rw [one_smul]
  have hcircle (t : unitInterval) (x : X0) :
      (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x := by
    change (Q0 (hamiltonZeroTargetVectorTranslation
      ((t : ℝ) • w x, hamiltonZeroAmbientMap phi x))).2 = _
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    simp only [Pi.smul_apply, smul_eq_mul, hnormal, mul_zero, AddCircle.coe_zero, add_zero]
    exact hamiltonZeroAmbientMap_circle phi x
  refine ⟨G, fun _ _ => rfl, hGzero, ?_, hcircle, ?_, ?_⟩
  · intro t x hx
    change hamiltonZeroTargetVectorTranslation ((t : ℝ) • w x, _) = _
    rw [hzero x hx, smul_zero, hamiltonZeroTargetVectorTranslation_zero]
  · intro x
    rw [hGone, hamiltonZeroTargetVectorTranslation_coordinates]
  · refine ⟨?_, ⟨hamiltonZeroHandleHomotopy phi G hGzero⟩,
      ⟨F.trans (hamiltonZeroHandleHomotopy phi G hGzero)⟩, ?_⟩
    · rw [hamiltonZeroHandleMap_domain]
      let g : C(X0, X0) :=
        ⟨fun x => hamiltonZeroTargetVectorTranslation (w x, hamiltonZeroAmbientMap phi x),
          hamiltonZeroTargetVectorTranslation.continuous.comp
            (w.continuous.prodMk (hamiltonZeroAmbientMap phi).continuous)⟩
      have hgeq : (⟨fun x => G (1, x),
          G.continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(X0, X0)) = g :=
        ContinuousMap.ext hGone
      rw [hgeq]
      exact chartwisePL_hamiltonZero_vector_translation hd hphi w hw
    · apply ContinuousMap.ext
      intro x
      rw [← hamiltonZeroAmbientMap_circle, hamiltonZeroAmbientMap_handle]
      exact hcircle 1 x

end PoincareConjecture.M76
