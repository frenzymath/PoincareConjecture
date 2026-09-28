import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarCoordinates











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem collar_radius_bounds {side s : ℝ} (hside : side * side = 1)
    (hs : s ∈ Ioo (-1) 1) : 0 < 1 + side * s ∧ 1 + side * s < 2 := by
  rcases mul_self_eq_one_iff.mp hside with rfl | rfl <;>
    constructor <;> nlinarith [hs.1, hs.2]



theorem exists_collar_radial_coordinates
    (g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    {side : ℝ} (hside : side * side = 1) :
    ∃ e : OpenPartialHomeomorph E3 (UnitTwoSphere × ℝ),
      e.source = {x | 0 < ‖x‖ ∧ ‖x‖ < 2} ∧
      e.target = univ ×ˢ Ioo (-1) 1 ∧
      (∀ x, e x = (g.symm (sphereDirection x), side * (‖x‖ - 1))) ∧
      (∀ p, e.symm p = (1 + side * p.2) • (g p.1 : E3)) ∧
      ContMDiffOn 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e e.source ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ e.symm e.target := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let U : Set E3 := {x | 0 < ‖x‖ ∧ ‖x‖ < 2}
  let f : E3 → UnitTwoSphere × ℝ :=
    fun x => (g.symm (sphereDirection x), side * (‖x‖ - 1))
  let k : UnitTwoSphere × ℝ → E3 := fun p => (1 + side * p.2) • (g p.1 : E3)
  have hf : ContMDiffOn 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f U := by
    have hdir := sphereDirection_contMDiffOn.mono
      (show U ⊆ ({0}ᶜ : Set E3) from fun _ hx => norm_pos_iff.mp hx.1)
    have hn : ContDiffOn ℝ ∞ (fun x : E3 => ‖x‖) U :=
      fun _ hx => (contDiffAt_norm ℝ (norm_pos_iff.mp hx.1)).contDiffWithinAt
    have hs : ContDiffOn ℝ ∞ (fun x : E3 => side * (‖x‖ - 1)) U :=
      contDiffOn_const.mul (hn.sub contDiffOn_const)
    exact (g.symm.contMDiff.comp_contMDiffOn hdir).prodMk
      hs.contMDiffOn
  have hk : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ k := by
    have ha : ContDiff ℝ ∞ (fun s : ℝ => 1 + side * s) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    have hs : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : UnitTwoSphere × ℝ => 1 + side * p.2) :=
      ha.contMDiff.comp contMDiff_snd
    have hg : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
        (fun p : UnitTwoSphere × ℝ => (g p.1 : E3)) :=
      contMDiff_coe_sphere.comp (g.contMDiff.comp contMDiff_fst)
    exact hs.smul hg
  let e : OpenPartialHomeomorph E3 (UnitTwoSphere × ℝ) := {
    toFun := f
    invFun := k
    source := U
    target := univ ×ˢ Ioo (-1) 1
    map_source' := by
      intro x hx
      refine ⟨mem_univ _, ?_⟩
      rcases mul_self_eq_one_iff.mp hside with hs | hs <;>
        simp only [f, hs, one_mul, neg_one_mul] <;>
        constructor <;> linarith [hx.1, hx.2]
    map_target' := by
      intro p hp
      have hr := collar_radius_bounds hside hp.2
      change 0 < ‖k p‖ ∧ ‖k p‖ < 2
      simpa only [k, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
        norm_eq_of_mem_sphere, mul_one] using hr
    left_inv' := by
      intro x hx
      change (1 + side * (side * (‖x‖ - 1))) •
        (g (g.symm (sphereDirection x)) : E3) = x
      rw [g.apply_symm_apply]
      have hr : 1 + side * (side * (‖x‖ - 1)) = ‖x‖ := by
        rw [← mul_assoc, hside, one_mul]
        ring
      rw [hr, sphereDirection_coe (norm_pos_iff.mp hx.1)]
      exact NormedSpace.norm_smul_normalize x
    right_inv' := by
      intro p hp
      have hr := collar_radius_bounds hside hp.2
      apply Prod.ext
      · change g.symm (sphereDirection ((1 + side * p.2) • (g p.1 : E3))) = p.1
        rw [sphereDirection_smul (g p.1) hr.1, g.symm_apply_apply]
      · change side * (‖(1 + side * p.2) • (g p.1 : E3)‖ - 1) = p.2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, norm_eq_of_mem_sphere,
          mul_one, add_sub_cancel_left, ← mul_assoc, hside, one_mul]
    open_source := (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
    open_target := isOpen_univ.prod isOpen_Ioo
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hk.continuous.continuousOn }
  exact ⟨e, rfl, rfl, fun _ => rfl, fun _ => rfl, hf, hk.contMDiffOn⟩



theorem exists_radial_collar_chart (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ)
    (g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    {side : ℝ} (hside : side * side = 1) :
    ∃ R : OpenPartialHomeomorph E3 E3,
      R.source = {x | 0 < ‖x‖ ∧ ‖x‖ < 2} ∧
      (∀ x, R x = ψ (g.symm (sphereDirection x), side * (‖x‖ - 1))) ∧
      ContDiffOn ℝ ∞ R R.source ∧ ContDiffOn ℝ ∞ R.symm R.target ∧
      ∀ (q : UnitTwoSphere) (s : ℝ), -1 < s → s < 1 →
        R ((1 + s) • (g q : E3)) = ψ (q, side * s) := by
  obtain ⟨e, hes, het, hef, _, he, hei⟩ := exists_collar_radial_coordinates g hside
  obtain ⟨c, hcf, hcs, _, hci⟩ := exists_collar_chart ψ hψ
  let R := e.trans c
  have hRs : R.source = e.source := by
    apply Set.Subset.antisymm inter_subset_left
    intro x hx
    exact ⟨hx, hcs.symm ▸ (het ▸ e.map_source hx)⟩
  have hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ c c.source := by
    simpa only [hcf, hcs] using hψ.1
  have hsmooth : ContDiffOn ℝ ∞ R R.source :=
    (hc.comp (he.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hinv : ContDiffOn ℝ ∞ R.symm R.target :=
    (hei.comp (hci.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  have hformula (x : E3) : R x =
      ψ (g.symm (sphereDirection x), side * (‖x‖ - 1)) := by
    change c (e x) = _
    rw [hcf, hef]
  refine ⟨R, hRs.trans hes, hformula, hsmooth, hinv, ?_⟩
  intro q s hs _hs'
  have hr : 0 < 1 + s := by linarith
  rw [hformula, sphereDirection_smul (g q) hr, g.symm_apply_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere,
    mul_one, add_sub_cancel_left]

end PoincareConjecture.M25.Topology3D
