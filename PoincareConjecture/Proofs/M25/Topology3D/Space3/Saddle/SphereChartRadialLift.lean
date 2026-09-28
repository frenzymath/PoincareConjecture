import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_sphere_chart_radial_lift
    (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (Q : OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ Q.symm Q.target) :
    ∃ E : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3,
      E.source = Q.source ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2) ∧
      E.target = {y : E3 | 1 / 2 < ‖F.symm y‖ ∧
        ‖F.symm y‖ < 3 / 2 ∧ sphereDirection (F.symm y) ∈ Q.target} ∧
      ContDiffOn ℝ ∞ E E.source ∧
      ContDiffOn ℝ ∞ E.symm E.target ∧
      (∀ z : (ℝ × ℝ) × ℝ, E z = F ((1 + z.2) • (Q z.1 : E3))) ∧
      (∀ y : E3, E.symm y =
        (Q.symm (sphereDirection (F.symm y)), ‖F.symm y‖ - 1)) ∧
      (∀ z ∈ E.source, ‖F.symm (E z)‖ = 1 + z.2) ∧
      (∀ z ∈ E.source,
        sphereDirection (F.symm (E z)) = Q z.1) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let U : Set ((ℝ × ℝ) × ℝ) := Q.source ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2)
  let A : Set E3 := {y | 1 / 2 < ‖F.symm y‖ ∧ ‖F.symm y‖ < 3 / 2}
  let T : Set E3 := {y | 1 / 2 < ‖F.symm y‖ ∧
    ‖F.symm y‖ < 3 / 2 ∧ sphereDirection (F.symm y) ∈ Q.target}
  let P : ((ℝ × ℝ) × ℝ) → E3 := fun z => F ((1 + z.2) • (Q z.1 : E3))
  let G : E3 → ((ℝ × ℝ) × ℝ) := fun y =>
    (Q.symm (sphereDirection (F.symm y)), ‖F.symm y‖ - 1)
  have hU : IsOpen U := Q.open_source.prod isOpen_Ioo
  have hA : IsOpen A :=
    (isOpen_lt continuous_const F.symm.continuous.norm).inter
      (isOpen_lt F.symm.continuous.norm continuous_const)
  have hAnonzero (y : E3) (hy : y ∈ A) : F.symm y ≠ 0 := by
    intro heq
    have hlt : 1 / 2 < ‖F.symm y‖ := hy.1
    rw [heq, norm_zero] at hlt
    linarith
  have hdir : ContMDiffOn 𝓘(ℝ, E3) (𝓡 2) ∞
      (fun y : E3 => sphereDirection (F.symm y)) A :=
    sphereDirection_contMDiffOn.comp F.symm.contMDiff.contMDiffOn
      (fun y hy => hAnonzero y hy)
  have hT : IsOpen T := by
    have heq : T = A ∩ (fun y : E3 => sphereDirection (F.symm y)) ⁻¹' Q.target := by
      apply Set.ext
      intro y
      exact and_assoc.symm
    rw [heq]
    exact hdir.continuousOn.isOpen_inter_preimage hA Q.open_target
  have hTA : T ⊆ A := fun _ hy => ⟨hy.1, hy.2.1⟩
  have hQambient : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (Q z : E3)) Q.source :=
    (contMDiff_coe_sphere.comp_contMDiffOn hQ).contDiffOn
  have hQsource : ContDiffOn ℝ ∞
      (fun z : (ℝ × ℝ) × ℝ => (Q z.1 : E3)) U :=
    hQambient.comp contDiff_fst.contDiffOn (fun _ hz => hz.1)
  have hP : ContDiffOn ℝ ∞ P U :=
    F.contDiff.comp_contDiffOn
      ((contDiffOn_const.add contDiff_snd.contDiffOn).smul hQsource)
  have hGfirst : ContDiffOn ℝ ∞
      (fun y : E3 => Q.symm (sphereDirection (F.symm y))) T :=
    (hQi.comp (hdir.mono hTA) (fun _ hy => hy.2.2)).contDiffOn
  have hGsecond : ContDiffOn ℝ ∞ (fun y : E3 => ‖F.symm y‖ - 1) T := by
    intro y hy
    exact (((contDiffAt_norm ℝ (hAnonzero y (hTA hy))).comp y
      F.symm.contDiff.contDiffAt).sub contDiffAt_const).contDiffWithinAt
  have hG : ContDiffOn ℝ ∞ G T := hGfirst.prodMk hGsecond
  have hpositive (z : (ℝ × ℝ) × ℝ) (hz : z ∈ U) : 0 < 1 + z.2 := by
    have hlow : -1 / 2 < z.2 := hz.2.1
    linarith
  have hnorm (z : (ℝ × ℝ) × ℝ) (hz : z ∈ U) :
      ‖F.symm (P z)‖ = 1 + z.2 := by
    simp only [P, F.symm_apply_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hpositive z hz), norm_eq_of_mem_sphere, mul_one]
  have hdirection (z : (ℝ × ℝ) × ℝ) (hz : z ∈ U) :
      sphereDirection (F.symm (P z)) = Q z.1 := by
    simp only [P, F.symm_apply_apply]
    exact sphereDirection_smul (Q z.1) (hpositive z hz)
  have hmap (z : (ℝ × ℝ) × ℝ) (hz : z ∈ U) : P z ∈ T := by
    change 1 / 2 < ‖F.symm (P z)‖ ∧ ‖F.symm (P z)‖ < 3 / 2 ∧
      sphereDirection (F.symm (P z)) ∈ Q.target
    rw [hnorm z hz, hdirection z hz]
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2], Q.map_source hz.1⟩
  have hback (y : E3) (hy : y ∈ T) : G y ∈ U := by
    change Q.symm (sphereDirection (F.symm y)) ∈ Q.source ∧
      ‖F.symm y‖ - 1 ∈ Ioo (-1 / 2 : ℝ) (1 / 2)
    exact ⟨Q.map_target hy.2.2, by linarith [hy.1], by linarith [hy.2.1]⟩
  have hleft (z : (ℝ × ℝ) × ℝ) (hz : z ∈ U) : G (P z) = z := by
    change (Q.symm (sphereDirection (F.symm (P z))), ‖F.symm (P z)‖ - 1) = z
    rw [hdirection z hz, hnorm z hz, Q.left_inv hz.1]
    apply Prod.ext
    · rfl
    · change 1 + z.2 - 1 = z.2
      exact add_sub_cancel_left 1 z.2
  have hright (y : E3) (hy : y ∈ T) : P (G y) = y := by
    have hrec : ‖F.symm y‖ • (sphereDirection (F.symm y) : E3) = F.symm y := by
      rw [sphereDirection_coe (hAnonzero y (hTA hy))]
      exact NormedSpace.norm_smul_normalize (F.symm y)
    calc
      P (G y) = F (‖F.symm y‖ • (sphereDirection (F.symm y) : E3)) := by
        simp only [P, G, Q.right_inv hy.2.2]
        congr 2
        linarith
      _ = F (F.symm y) := congrArg F hrec
      _ = y := F.apply_symm_apply y
  let E : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3 :=
    { toFun := P
      invFun := G
      source := U
      target := T
      map_source' := hmap
      map_target' := hback
      left_inv' := hleft
      right_inv' := hright
      open_source := hU
      open_target := hT
      continuousOn_toFun := hP.continuousOn
      continuousOn_invFun := hG.continuousOn }
  exact ⟨E, rfl, rfl, hP, hG, fun _ => rfl, fun _ => rfl, hnorm, hdirection⟩

end PoincareConjecture.M25.Topology3D
