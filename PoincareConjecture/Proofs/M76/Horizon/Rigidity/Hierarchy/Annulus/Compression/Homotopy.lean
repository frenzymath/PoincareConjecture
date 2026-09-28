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
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.exists_hamiltonZero_second_coordinate_homotopy {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (w : C(X0, ℝ))
    (hw : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    {U : Set X0} (hzero : ∀ x, x ∉ U → w x = 0) :
    ∃ (psi : C(H0, H0)) (G : C(unitInterval × X0, X0)),
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ x, G (1, x) = hamiltonZeroAmbientMap psi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ U →
        G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).1.1 = (Q0 (hamiltonZeroAmbientMap phi x)).1.1) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      ∀ x, hamiltonZeroSecondCircleMap psi x =
        hamiltonZeroSecondCircleMap phi x + (w x : C0) := by
  classical
  let v : C(X0, V3) := ⟨fun x j => if j = 1 then w x else 0,
    continuous_pi (fun j => by split_ifs <;> fun_prop)⟩
  have hv (i : ι) : LocallyPiecewiseAffineOn (v ∘ (e i).symm) (e i).target := by
    apply LocallyPiecewiseAffineOn.pi (e i).open_target
    intro j
    by_cases hj : j = 1
    · simpa only [Function.comp_def, v, ContinuousMap.coe_mk, hj, if_true] using hw i
    · exact (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (0 : ℝ))
          (e i).open_target).congr (fun _ _ => by simp [v, hj])
  obtain ⟨G, hG, hstart, hfixed, hnormal, htangent, hPL, hF, hF0, hphase⟩ :=
    hphi.exists_hamiltonZero_tangential_homotopy hd F v hv
      (fun _ => by simp [v]) (fun x hx => by ext j; simp [v, hzero x hx])
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨hamiltonZeroHandleMap g, G, hstart, ?_, hfixed, hnormal, ?_,
    hPL, hF, hF0, hphase, ?_⟩
  · intro x
    rw [hamiltonZeroAmbientMap_handle]
    rfl
  · intro t x
    rw [hG, hamiltonZeroTargetVectorTranslation_coordinates]
    simp [v]
  · intro x
    rw [hamiltonZeroSecondCircleMap_ambient, hamiltonZeroAmbientMap_handle]
    change (Q0 (G (1, x))).1.2 = _
    rw [htangent]
    rw [hamiltonZeroSecondCircleMap_ambient]
    rfl

end PoincareConjecture.M76
