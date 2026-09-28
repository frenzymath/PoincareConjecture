import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Matrix

namespace PoincareConjecture.M25.Topology3D



theorem exists_nonnested_reference_lower_planar_chart
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (i : Fin 2) :
    let eps : ℝ := (![1, -1] : Fin 2 → ℝ) i
    let D := {p : ℝ × ℝ | |p.2| < 7 / 16 ∧
      0 < 3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2}
    let V := {x : E2 | 0 < eps * (J2 x).2 ∧
      31 / 256 < 2 * ‖x‖ ^ 2 ∧ 2 * ‖x‖ ^ 2 < 255 / 256}
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) E2,
      e.source = D ∧ e.target = V ∧
      (∀ p : ℝ × ℝ, e p = J2.symm (p.1 / Real.sqrt 2,
        eps * Real.sqrt (3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2) / Real.sqrt 2)) ∧
      (∀ x : E2, e.symm x =
        (Real.sqrt 2 * (J2 x).1, 1 / 2 - Real.sqrt (1 - 2 * ‖x‖ ^ 2))) ∧
      ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.source, 2 * ‖e p‖ ^ 2 = 3 / 4 + p.2 - p.2 ^ 2) ∧
      ∀ r : ℝ, 0 ≤ r → r < 7 / 16 →
        {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2} ⊆ e.source := by
  classical
  dsimp only
  let eps : ℝ := (![1, -1] : Fin 2 → ℝ) i
  let Q : ℝ × ℝ → ℝ := fun p => 3 / 4 + p.2 - p.1 ^ 2 - p.2 ^ 2
  let D : Set (ℝ × ℝ) := {p | |p.2| < 7 / 16 ∧ 0 < Q p}
  let V : Set E2 := {x | 0 < eps * (J2 x).2 ∧
    31 / 256 < 2 * ‖x‖ ^ 2 ∧ 2 * ‖x‖ ^ 2 < 255 / 256}
  let F : ℝ × ℝ → E2 := fun p =>
    J2.symm (p.1 / Real.sqrt 2, eps * Real.sqrt (Q p) / Real.sqrt 2)
  let G : E2 → ℝ × ℝ := fun x =>
    (Real.sqrt 2 * (J2 x).1, 1 / 2 - Real.sqrt (1 - 2 * ‖x‖ ^ 2))
  have heps : eps ^ 2 = 1 := by fin_cases i <;> norm_num [eps]
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have htwoSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hQ : ContDiff ℝ ∞ Q := by dsimp [Q]; fun_prop
  have hnorm : ContDiff ℝ ∞ (fun x : E2 => ‖x‖ ^ 2) := by
    have heq : (fun x : E2 => ‖x‖ ^ 2) =
        (fun x : E2 => (J2 x).1 ^ 2 + (J2 x).2 ^ 2) :=
      funext (fun x => (hJ2 x).symm)
    rw [heq]
    exact (J2.contDiff.fst.pow 2).add (J2.contDiff.snd.pow 2)
  have hD : IsOpen D :=
    (isOpen_lt continuous_snd.abs continuous_const).inter
      (isOpen_lt continuous_const hQ.continuous)
  have hV : IsOpen V :=
    (isOpen_lt continuous_const
      (continuous_const.mul J2.continuous.snd)).inter
      ((isOpen_lt continuous_const (continuous_const.mul hnorm.continuous)).inter
        (isOpen_lt (continuous_const.mul hnorm.continuous) continuous_const))
  have hF : ContDiffOn ℝ ∞ F D := by
    apply J2.symm.contDiff.comp_contDiffOn
    exact (contDiff_fst.contDiffOn.div_const _).prodMk
      ((contDiffOn_const.mul (hQ.contDiffOn.sqrt
        (fun p hp => hp.2.ne'))).div_const _)
  have hG : ContDiffOn ℝ ∞ G V := by
    exact (contDiffOn_const.mul J2.contDiff.fst.contDiffOn).prodMk
      (contDiffOn_const.sub ((contDiff_const.sub
        (contDiff_const.mul hnorm)).contDiffOn.sqrt (fun x hx => by
          have hx' : 2 * ‖x‖ ^ 2 < 255 / 256 := hx.2.2
          apply ne_of_gt
          linarith)))
  have hFnorm (p : ℝ × ℝ) (hp : p ∈ D) :
      2 * ‖F p‖ ^ 2 = 3 / 4 + p.2 - p.2 ^ 2 := by
    rw [← hJ2 (F p)]
    simp only [F, ContinuousLinearEquiv.apply_symm_apply, div_pow, mul_pow,
      heps, htwoSq, Real.sq_sqrt hp.2.le, one_mul]
    dsimp [Q]
    ring
  have hFmap (p : ℝ × ℝ) (hp : p ∈ D) : F p ∈ V := by
    have hblo : -7 / 16 < p.2 := by simpa only [neg_div] using (abs_lt.mp hp.1).1
    have hbhi : p.2 < 7 / 16 := (abs_lt.mp hp.1).2
    refine ⟨?_, ?_, ?_⟩
    · have heq : eps * (J2 (F p)).2 = Real.sqrt (Q p) / Real.sqrt 2 := by
        simp only [F, ContinuousLinearEquiv.apply_symm_apply]
        calc
          eps * (eps * Real.sqrt (Q p) / Real.sqrt 2) =
              eps ^ 2 * Real.sqrt (Q p) / Real.sqrt 2 := by ring
          _ = Real.sqrt (Q p) / Real.sqrt 2 := by rw [heps, one_mul]
      rw [heq]
      exact div_pos (Real.sqrt_pos.2 hp.2) htwo
    · rw [hFnorm p hp]
      have hh := mul_pos (show 0 < p.2 + 7 / 16 by linarith)
        (show 0 < 23 / 16 - p.2 by linarith)
      nlinarith only [hh]
    · rw [hFnorm p hp]
      have hh := mul_pos (show 0 < 7 / 16 - p.2 by linarith)
        (show 0 < 9 / 16 - p.2 by linarith)
      nlinarith only [hh]
  have hGF (p : ℝ × ℝ) (hp : p ∈ D) : G (F p) = p := by
    have hb : 0 < 1 / 2 - p.2 := by
      have := (abs_lt.mp hp.1).2
      linarith
    have heq : 1 - 2 * ‖F p‖ ^ 2 = (1 / 2 - p.2) ^ 2 := by
      rw [hFnorm p hp]
      ring
    have hroot : Real.sqrt (1 - 2 * ‖F p‖ ^ 2) = 1 / 2 - p.2 := by
      rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos hb]
    apply Prod.ext
    · change Real.sqrt 2 * (J2 (F p)).1 = p.1
      simp only [F, ContinuousLinearEquiv.apply_symm_apply]
      field_simp [htwo.ne']
    · change 1 / 2 - Real.sqrt (1 - 2 * ‖F p‖ ^ 2) = p.2
      rw [hroot]
      ring
  have hGdata (x : E2) (hx : x ∈ V) :
      G x ∈ D ∧ Q (G x) = 2 * (J2 x).2 ^ 2 := by
    have hr : 0 < 1 - 2 * ‖x‖ ^ 2 := by linarith [hx.2.2]
    have hs : Real.sqrt (1 - 2 * ‖x‖ ^ 2) ^ 2 = 1 - 2 * ‖x‖ ^ 2 :=
      Real.sq_sqrt hr.le
    have hs0 : 0 ≤ Real.sqrt (1 - 2 * ‖x‖ ^ 2) := Real.sqrt_nonneg _
    have hslo : 1 / 16 < Real.sqrt (1 - 2 * ‖x‖ ^ 2) := by
      apply (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 16) hs0).mp
      nlinarith only [hs, hx.2.2]
    have hshi : Real.sqrt (1 - 2 * ‖x‖ ^ 2) < 15 / 16 := by
      apply (sq_lt_sq₀ hs0 (by norm_num : (0 : ℝ) ≤ 15 / 16)).mp
      nlinarith only [hs, hx.2.1]
    have hy : (J2 x).2 ≠ 0 := by
      intro hy
      have hh := hx.1
      rw [hy, mul_zero] at hh
      exact (lt_irrefl 0) hh
    have henergy : Q (G x) = 2 * (J2 x).2 ^ 2 := by
      dsimp [Q, G]
      simp only [mul_pow, htwoSq]
      nlinarith only [hs, hJ2 x]
    refine ⟨⟨?_, ?_⟩, henergy⟩
    · change |1 / 2 - Real.sqrt (1 - 2 * ‖x‖ ^ 2)| < 7 / 16
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · rw [henergy]
      exact mul_pos (by norm_num) (sq_pos_of_ne_zero hy)
  have hFG (x : E2) (hx : x ∈ V) : F (G x) = x := by
    have hroot : Real.sqrt (Q (G x)) = Real.sqrt 2 * (eps * (J2 x).2) := by
      apply (Real.sqrt_eq_iff_eq_sq (hGdata x hx).1.2.le
        (mul_pos htwo hx.1).le).2
      rw [(hGdata x hx).2, mul_pow, mul_pow, htwoSq, heps]
      ring
    apply J2.injective
    simp only [F, ContinuousLinearEquiv.apply_symm_apply]
    apply Prod.ext
    · change (Real.sqrt 2 * (J2 x).1) / Real.sqrt 2 = (J2 x).1
      field_simp [htwo.ne']
    · change eps * Real.sqrt (Q (G x)) / Real.sqrt 2 = (J2 x).2
      rw [hroot]
      calc
        eps * (Real.sqrt 2 * (eps * (J2 x).2)) / Real.sqrt 2 =
            eps ^ 2 * (J2 x).2 := by field_simp [htwo.ne']
        _ = (J2 x).2 := by rw [heps, one_mul]
  let e : OpenPartialHomeomorph (ℝ × ℝ) E2 :=
    { toFun := F, invFun := G, source := D, target := V
      map_source' := hFmap
      map_target' := fun x hx => (hGdata x hx).1
      left_inv' := hGF, right_inv' := hFG
      open_source := hD, open_target := hV
      continuousOn_toFun := hF.continuousOn
      continuousOn_invFun := hG.continuousOn }
  refine ⟨e, rfl, rfl, fun _ => rfl, fun _ => rfl, hF, hG, hFnorm, ?_⟩
  intro r hr hrl p hp
  change p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2 at hp
  change |p.2| < 7 / 16 ∧ 0 < Q p
  have hp2 : |p.2| ≤ r := by
    apply (sq_le_sq₀ (abs_nonneg p.2) hr).mp
    rw [sq_abs]
    nlinarith only [hp, sq_nonneg p.1]
  have hp2lo : -r ≤ p.2 := by
    have hh := neg_abs_le p.2
    linarith
  refine ⟨hp2.trans_lt hrl, ?_⟩
  have hmargin := mul_pos (sub_pos.mpr hrl)
    (show 0 < 23 / 16 + r by linarith)
  dsimp [Q]
  nlinarith only [hmargin, hp2lo, hp]

end PoincareConjecture.M25.Topology3D
