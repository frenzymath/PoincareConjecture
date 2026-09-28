import PoincareConjecture.Proofs.M25.Mathlib.PositivePolar
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CollarAbsorption











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D.DiffSphereIsotopyData




theorem exists_normPreserving_radialExtension
    {f : UnitTwoSphere → UnitTwoSphere} (D : DiffSphereIsotopyData f)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x, ‖d x‖ = ‖x‖) ∧
      (∀ x, ‖d.symm x‖ = ‖x‖) ∧
      EqOn (d : E3 → E3) D.isometry (closedBall 0 a) ∧
      EqOn (d.symm : E3 → E3) D.isometry.symm (closedBall 0 a) ∧
      (∀ (q : UnitTwoSphere) (r : ℝ), b ≤ r →
        d (r • q.val) = r • (f q).val) ∧
      (∀ (q : UnitTwoSphere) (r : ℝ), b ≤ r →
        d.symm (r • (f q).val) = r • q.val) ∧
      (∀ R : ℝ, d '' ball 0 R = ball 0 R) ∧
      (∀ R : ℝ, d '' closedBall 0 R = closedBall 0 R) := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  obtain ⟨q0, hq0⟩ := (NormedSpace.sphere_nonempty (E := E3)).mpr
    (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨Q, hQs, hQt, hQf, hQheight, hQnormal, hQ, hQi⟩ :=
    exists_smooth_unitSpherePolar (n := 2) (⟨q0, hq0⟩ : UnitTwoSphere)
  let T := D.collarDiffeomorph a b
  have hTheight (p : UnitTwoSphere × ℝ) : (T p).2 = p.2 := rfl
  have hTiheight (p : UnitTwoSphere × ℝ) : (T.symm p).2 = p.2 := rfl
  have hQtmem {x : E3} (hx : x ≠ 0) : x ∈ Q.target := by
    simpa only [hQt, mem_compl_iff, mem_singleton_iff] using hx
  have hQnorm (p : UnitTwoSphere × ℝ) (hp : 0 < p.2) : ‖Q p‖ = p.2 := by
    rw [hQf, norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp p.1.property,
      mul_one, abs_of_pos hp]
  have hTsource {x : E3} (hx : x ≠ 0) : T (Q.symm x) ∈ Q.source := by
    rw [hQs]
    exact ⟨mem_univ _, by rw [hTheight, hQheight]; exact norm_pos_iff.mpr hx⟩
  have hTisource {x : E3} (hx : x ≠ 0) : T.symm (Q.symm x) ∈ Q.source := by
    rw [hQs]
    exact ⟨mem_univ _, by rw [hTiheight, hQheight]; exact norm_pos_iff.mpr hx⟩
  let F : E3 → E3 := fun x => if x = 0 then 0 else Q (T (Q.symm x))
  let G : E3 → E3 := fun x => if x = 0 then 0 else Q (T.symm (Q.symm x))
  have hF {x : E3} (hx : x ≠ 0) : F x = Q (T (Q.symm x)) := if_neg hx
  have hG {x : E3} (hx : x ≠ 0) : G x = Q (T.symm (Q.symm x)) := if_neg hx
  have hFnorm (x : E3) : ‖F x‖ = ‖x‖ := by
    by_cases hx : x = 0
    · simp [F, hx]
    · rw [hF hx, hQnorm _ (by rw [hTheight, hQheight]; exact norm_pos_iff.mpr hx),
        hTheight, hQheight]
  have hGnorm (x : E3) : ‖G x‖ = ‖x‖ := by
    by_cases hx : x = 0
    · simp [G, hx]
    · rw [hG hx, hQnorm _ (by rw [hTiheight, hQheight]; exact norm_pos_iff.mpr hx),
        hTiheight, hQheight]
  have hFne {x : E3} (hx : x ≠ 0) : F x ≠ 0 :=
    norm_pos_iff.mp (by rw [hFnorm]; exact norm_pos_iff.mpr hx)
  have hGne {x : E3} (hx : x ≠ 0) : G x ≠ 0 :=
    norm_pos_iff.mp (by rw [hGnorm]; exact norm_pos_iff.mpr hx)
  have hGF (x : E3) : G (F x) = x := by
    by_cases hx : x = 0
    · simp [F, G, hx]
    · rw [hG (hFne hx), hF hx, Q.left_inv (hTsource hx), T.symm_apply_apply,
        Q.right_inv (hQtmem hx)]
  have hFG (x : E3) : F (G x) = x := by
    by_cases hx : x = 0
    · simp [F, G, hx]
    · rw [hF (hGne hx), hG hx, Q.left_inv (hTisource hx), T.apply_symm_apply,
        Q.right_inv (hQtmem hx)]
  have hFnear : EqOn F D.isometry (closedBall 0 a) := by
    intro x hxball
    by_cases hx : x = 0
    · simp [F, hx]
    · have hxn : ‖x‖ ≤ a := mem_closedBall_zero_iff.mp hxball
      have ht := D.collarDiffeomorph_eq_isometry hab (Q.symm x)
        (by rw [hQheight]; exact hxn)
      rw [hF hx, ht, hQf, hQheight]
      change ‖x‖ • D.isometry (Q.symm x).1.val = D.isometry x
      rw [hQnormal x hx, map_smul, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hGnear : EqOn G D.isometry.symm (closedBall 0 a) := by
    intro x hx
    have hGball : G x ∈ closedBall 0 a := by
      simpa only [mem_closedBall_zero_iff, hGnorm] using hx
    apply D.isometry.injective
    rw [D.isometry.apply_symm_apply, ← hFnear hGball, hFG]
  have hsmooth (H : E3 → E3)
      (K : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (UnitTwoSphere × ℝ) (UnitTwoSphere × ℝ) ∞)
      (A : E3 ≃ₗᵢ[ℝ] E3) (hnear : EqOn H A (closedBall 0 a))
      (haway : ∀ x ≠ 0, H x = Q (K (Q.symm x))) :
      ContMDiff (𝓡 3) (𝓡 3) ∞ H := by
    intro x
    by_cases hx : x = 0
    · subst x
      have hA : ContMDiff (𝓡 3) (𝓡 3) ∞ (A : E3 → E3) :=
        A.toContinuousLinearEquiv.toDiffeomorph.contMDiff
      apply hA.contMDiffAt.congr_of_eventuallyEq
      filter_upwards [ball_mem_nhds (0 : E3) ha] with y hy
      exact hnear (ball_subset_closedBall hy)
    · have hlocal : ContMDiffOn (𝓡 3) (𝓡 3) ∞
          (fun y => Q (K (Q.symm y))) Q.target :=
        hQ.comp_contMDiffOn (K.contMDiff.comp_contMDiffOn hQi)
      apply (hlocal.contMDiffAt (Q.open_target.mem_nhds (hQtmem hx))).congr_of_eventuallyEq
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      exact haway y hy
  let d : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
    { toFun := F
      invFun := G
      left_inv := hGF
      right_inv := hFG
      contMDiff_toFun := hsmooth F T D.isometry hFnear (fun _ hx => hF hx)
      contMDiff_invFun := hsmooth G T.symm D.isometry.symm hGnear (fun _ hx => hG hx) }
  have houter (q : UnitTwoSphere) (r : ℝ) (hr : b ≤ r) :
      d (r • q.val) = r • (f q).val := by
    have hrpos : 0 < r := (ha.trans hab).trans_le hr
    have hne : r • q.val ≠ 0 :=
      smul_ne_zero hrpos.ne' (ne_zero_of_mem_unit_sphere q)
    change F (r • q.val) = _
    rw [hF hne, ← hQf (q, r), Q.left_inv (by rw [hQs]; exact ⟨mem_univ _, hrpos⟩),
      D.collarDiffeomorph_eq_map hab (q, r) hr, hQf]
  refine ⟨d, hFnorm, hGnorm, hFnear, hGnear, houter, ?_, ?_, ?_⟩
  · intro q r hr
    calc
      d.symm (r • (f q).val) = d.symm (d (r • q.val)) := congrArg d.symm (houter q r hr).symm
      _ = r • q.val := d.symm_apply_apply _
  · intro R
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change F x ∈ ball 0 R
      simpa only [mem_ball_zero_iff, hFnorm] using hx
    · intro hy
      refine ⟨d.symm y, ?_, d.apply_symm_apply y⟩
      change G y ∈ ball 0 R
      simpa only [mem_ball_zero_iff, hGnorm] using hy
  · intro R
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change F x ∈ closedBall 0 R
      simpa only [mem_closedBall_zero_iff, hFnorm] using hx
    · intro hy
      refine ⟨d.symm y, ?_, d.apply_symm_apply y⟩
      change G y ∈ closedBall 0 R
      simpa only [mem_closedBall_zero_iff, hGnorm] using hy

end PoincareConjecture.M25.Topology3D.DiffSphereIsotopyData
