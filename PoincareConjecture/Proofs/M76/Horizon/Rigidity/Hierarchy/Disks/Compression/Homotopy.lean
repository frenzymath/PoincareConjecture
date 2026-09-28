import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.AmbientDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdPhaseGroups

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.exists_hamiltonZero_third_scalar_homotopy
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (w : C(X0, ℝ))
    (hwPL : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    {B : Set X0} (hwzero : ∀ x ∈ B, w x = 0) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (∀ x, hamiltonZeroThirdCircleMap psi x = hamiltonZeroThirdCircleMap phi x + (w x : C0)) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) B,
        ∀ t x, Q0 (G (t, x)) =
          (((Q0 (hamiltonZeroAmbientMap phi x)).1.1 + (((t : ℝ) * w x : ℝ) : C0),
            (Q0 (hamiltonZeroAmbientMap phi x)).1.2), (Q0 (hamiltonZeroAmbientMap phi x)).2) := by
  let W : C(X0, V3) := ⟨fun x => ![w x, 0, 0], by
    apply continuous_pi
    intro k
    fin_cases k
    · exact w.continuous
    · exact continuous_const
    · exact continuous_const⟩
  have hWPL (i : ι) : LocallyPiecewiseAffineOn (W ∘ (e i).symm) (e i).target := by
    apply LocallyPiecewiseAffineOn.pi (e i).open_target
    intro k
    fin_cases k
    · exact hwPL i
    · exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (0 : ℝ)) (e i).open_target
    · exact locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (0 : ℝ)) (e i).open_target
  have hWzero (x : X0) (hx : x ∈ B) : W x = 0 := by
    change ![w x, 0, 0] = 0
    rw [hwzero x hx]
    ext k
    fin_cases k <;> rfl
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hsecond, hvalue, _, _⟩ :=
    hphi.exists_hamiltonZero_second_phase_adjustment hd F W hWPL (fun _ => rfl) hWzero
  let G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) B := {
    toFun := fun z => hamiltonZeroTargetVectorTranslation
      ((z.1 : ℝ) • W z.2, hamiltonZeroAmbientMap phi z.2)
    continuous_toFun := hamiltonZeroTargetVectorTranslation.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).smul
        (W.continuous.comp continuous_snd)).prodMk
        ((hamiltonZeroAmbientMap phi).continuous.comp continuous_snd))
    map_zero_left := by intro x; change hamiltonZeroTargetVectorTranslation ((0 : ℝ) • W x, _) = _
                        rw [zero_smul, hamiltonZeroTargetVectorTranslation_zero]
    map_one_left := by intro x; change hamiltonZeroTargetVectorTranslation ((1 : ℝ) • W x, _) = _
                       rw [one_smul]; exact (hvalue x).symm
    prop' := by intro t x hx; change hamiltonZeroTargetVectorTranslation ((t : ℝ) • W x, _) = _
                rw [hWzero x hx, smul_zero, hamiltonZeroTargetVectorTranslation_zero] }
  have hG (t : unitInterval) (x : X0) : Q0 (G (t, x)) =
      (((Q0 (hamiltonZeroAmbientMap phi x)).1.1 + (((t : ℝ) * w x : ℝ) : C0),
        (Q0 (hamiltonZeroAmbientMap phi x)).1.2), (Q0 (hamiltonZeroAmbientMap phi x)).2) := by
    change Q0 (hamiltonZeroTargetVectorTranslation (_, _)) = _
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    simp [W, Pi.smul_apply, smul_eq_mul]
  refine ⟨psi, hpsi, Hpsi, Fpsi, ?_, hsecond, ?_, G, hG⟩
  · apply ContinuousMap.ext
    intro x
    have h := congrArg Prod.snd (hG 1 x)
    rw [G.apply_one] at h
    exact h
  · intro x
    have h := congrArg (fun z : (C0 × C0) × C0 => z.1.1) (hG 1 x)
    rw [G.apply_one] at h
    change hamiltonZeroThirdCircleMap psi x =
      hamiltonZeroThirdCircleMap phi x + (((1 : ℝ) * w x : ℝ) : C0) at h
    simpa only [one_mul] using h

end PoincareConjecture.M76
