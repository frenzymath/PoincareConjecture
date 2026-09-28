import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnitCubePLCollar
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => (Ico (0 : ℝ) (1 / 8))
local notation "B" => (closedBall (0 : V3) 1)
local notation "S0" => (sphere (0 : V3) 1)

variable {X : Type*} [TopologicalSpace X] {D S : Set X}

theorem exists_marked_brown_inward_collar
    (hD : IsUnitBallPair V3 D S) (s : S0 ≃ₜ S) :
    ∃ (phi : B ≃ₜ D) (U : Set D) (g : (S × I) ≃ₜ U),
      (∀ x : S0, phi ⟨x, sphere_subset_closedBall x.property⟩ =
        ⟨s x, hD.1 (s x).property⟩) ∧
      (∀ x : B, (x : V3) ∈ S0 ↔ (phi x : X) ∈ S) ∧
      U = {x | (7 / 8 : ℝ) < ‖(phi.symm x : V3)‖} ∧ IsOpen U ∧
      (∀ p : S × I, (phi.symm (g p : D) : V3) =
        unitCubeInwardCollarMap ((s.symm p.1 : V3), (p.2 : ℝ))) ∧
      (∀ p : S × I, ‖(phi.symm (g p : D) : V3)‖ = 1 - (p.2 : ℝ)) ∧
      (∀ p : S × I, (p.2 : ℝ) = 0 → ((g p : D) : X) = (p.1 : X)) ∧
      ∀ p : S × I, ((g p : D) : X) ∈ S ↔ (p.2 : ℝ) = 0 := by
  have hunit : IsUnitBallPair V3 B S0 :=
    ⟨sphere_subset_closedBall, Homeomorph.refl B, fun _ => Iff.rfl⟩
  obtain ⟨phi, hphi, hboundary⟩ := hunit.exists_extension hD s
  obtain ⟨F, _, hFval, hFnorm, hFzero⟩ := exists_unitCube_inward_finitePL_collar
  let C : Set (V3 × ℝ) := S0 ×ˢ Icc (0 : ℝ) (1 / 8)
  let T : Set V3 := (norm : V3 → ℝ) ⁻¹' Icc (7 / 8 : ℝ) 1
  let C0 : Set (V3 × ℝ) := S0 ×ˢ I
  let T0 : Set V3 := {x | (7 / 8 : ℝ) < ‖x‖ ∧ ‖x‖ ≤ 1}
  have hC : C0 ⊆ C := fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.le⟩
  have hT : T0 ⊆ T := fun _ hx => ⟨hx.1.le, hx.2⟩
  have hFT (p : C) : (p : V3 × ℝ) ∈ C0 ↔ (F p : V3) ∈ T0 := by
    change ((p : V3 × ℝ).1 ∈ S0 ∧
      0 ≤ (p : V3 × ℝ).2 ∧ (p : V3 × ℝ).2 < 1 / 8) ↔
      (7 / 8 : ℝ) < ‖(F p : V3)‖ ∧ ‖(F p : V3)‖ ≤ 1
    rw [hFnorm]
    constructor
    · intro hp
      constructor <;> linarith [hp.2.1, hp.2.2]
    · intro hp
      exact ⟨p.property.1, p.property.2.1, by linarith [hp.1]⟩
  let F0 : C0 ≃ₜ T0 := F.restrictSubsets hC hT hFT
  let U : Set D := {x | (7 / 8 : ℝ) < ‖(phi.symm x : V3)‖}
  have hU : IsOpen U := isOpen_lt continuous_const
    (continuous_norm.comp (continuous_subtype_val.comp phi.symm.continuous))
  let q : T0 ≃ₜ U := {
    toFun := fun x => ⟨phi ⟨x, mem_closedBall_zero_iff.mpr x.property.2⟩, by
      change (7 / 8 : ℝ) < ‖(phi.symm (phi _) : V3)‖
      rw [phi.symm_apply_apply]
      exact x.property.1⟩
    invFun := fun y => ⟨phi.symm y, y.property,
      mem_closedBall_zero_iff.mp (phi.symm y).property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change (phi.symm (phi _) : V3) = (x : V3)
      rw [phi.symm_apply_apply]
    right_inv := by
      intro y
      apply Subtype.ext
      exact phi.apply_symm_apply (y : D)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let a : (S × I) ≃ₜ C0 :=
    (s.symm.prodCongr (Homeomorph.refl I)).trans (Homeomorph.Set.prod S0 I).symm
  let g := (a.trans F0).trans q
  have hgval (p : S × I) : (phi.symm (g p : D) : V3) =
      unitCubeInwardCollarMap ((s.symm p.1 : V3), (p.2 : ℝ)) := by
    change (phi.symm (phi _) : V3) = _
    rw [phi.symm_apply_apply]
    exact hFval ⟨((s.symm p.1 : V3), (p.2 : ℝ)),
      (s.symm p.1).property, p.2.property.1, p.2.property.2.le⟩
  have hgnorm (p : S × I) : ‖(phi.symm (g p : D) : V3)‖ = 1 - (p.2 : ℝ) := by
    change ‖(phi.symm (phi _) : V3)‖ = _
    rw [phi.symm_apply_apply]
    exact hFnorm ⟨((s.symm p.1 : V3), (p.2 : ℝ)),
      (s.symm p.1).property, p.2.property.1, p.2.property.2.le⟩
  refine ⟨phi, U, g, hphi, hboundary, rfl, hU, hgval, hgnorm, ?_, ?_⟩
  · intro p hp
    have hcoord : (phi.symm (g p : D) : V3) = (s.symm p.1 : V3) := by
      change (phi.symm (phi _) : V3) = _
      rw [phi.symm_apply_apply]
      exact hFzero ⟨((s.symm p.1 : V3), (p.2 : ℝ)),
        (s.symm p.1).property, p.2.property.1, p.2.property.2.le⟩ hp
    have heq : (g p : D) = phi
        ⟨s.symm p.1, sphere_subset_closedBall (s.symm p.1).property⟩ := by
      apply phi.symm.injective
      rw [phi.symm_apply_apply]
      exact Subtype.ext hcoord
    rw [heq, hphi]
    exact congrArg Subtype.val (s.apply_symm_apply p.1)
  · intro p
    have heq := hboundary (phi.symm (g p : D))
    rw [phi.apply_symm_apply, mem_sphere_zero_iff_norm, hgnorm] at heq
    exact heq.symm.trans (sub_eq_self : 1 - (p.2 : ℝ) = 1 ↔ (p.2 : ℝ) = 0)

end PoincareConjecture.M76
