import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceBufferedChart
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_nested_native_source_chart
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (rho sigma : ℝ) (hrho : 0 < rho) (hsigma : sigma = 1 ∨ sigma = -1)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (hbuffer : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ (2 * rho) ^ 2} ⊆ e.target) :
    let sN : E2 → ℝ × ℝ := fun x =>
      (sigma * rho * (J2 x).2, sigma * rho * (J2 x).1)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    ∃ ks : OpenPartialHomeomorph E2 UnitTwoSphere,
      ks.source = {x : E2 | sN x ∈ e.target} ∧
      ks.target = e.source ∧
      (∀ x : E2, ks x = e.symm (sN x)) ∧
      (∀ p : UnitTwoSphere, ks.symm p = J2.symm
        (sigma / rho * (e p).2, sigma / rho * (e p).1)) ∧
      closedBall (0 : E2) 2 ⊆ ks.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ ks ks.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ ks.symm ks.target ∧
      ks '' ball (0 : E2) 1 =
        e.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} ∧
      ks '' closedBall (0 : E2) 1 =
        e.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ∧
      ∀ (z r : ℝ) (i : Fin 4),
        ks (J2.symm
          (sx i * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2),
            sy i * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2))) =
          e.symm
            (sigma * (sy i * Real.sqrt ((rho ^ 2 * r ^ 2 - z) / 2)),
              sigma * (sx i * Real.sqrt ((rho ^ 2 * r ^ 2 + z) / 2))) := by
  classical
  intro sN sx sy
  have hsigmaSq : sigma ^ 2 = 1 := by
    rcases hsigma with h | h <;> norm_num [h]
  let M : E2 ≃L[ℝ] (ℝ × ℝ) := {
    toFun := sN
    invFun := fun s => J2.symm (sigma / rho * s.2, sigma / rho * s.1)
    map_add' := by
      intro x y
      dsimp [sN]
      simp only [map_add, Prod.fst_add, Prod.snd_add]
      ring
    map_smul' := by
      intro a x
      dsimp [sN]
      simp only [map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    left_inv := by
      intro x
      change J2.symm (sigma / rho * (sN x).2,
        sigma / rho * (sN x).1) = x
      apply J2.injective
      rw [J2.apply_symm_apply]
      apply Prod.ext <;> dsimp [sN]
      · field_simp [hrho.ne']
        ring_nf
        rw [hsigmaSq]
        ring
      · field_simp [hrho.ne']
        ring_nf
        rw [hsigmaSq]
        ring
    right_inv := by
      intro s
      dsimp [sN]
      rw [J2.apply_symm_apply]
      apply Prod.ext <;> field_simp [hrho.ne'] <;> ring_nf <;> rw [hsigmaSq] <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let ks := M.toHomeomorph.toOpenPartialHomeomorph.trans e.symm
  have hsource : ks.source = {x : E2 | sN x ∈ e.target} := by
    ext x
    change (x ∈ (Set.univ : Set E2) ∧ sN x ∈ e.target) ↔ _
    simp
  have htarget : ks.target = e.source := by
    ext p
    change (p ∈ e.source ∧ e p ∈ (Set.univ : Set (ℝ × ℝ))) ↔ _
    simp
  have hks : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ ks ks.source := by
    exact hei.comp M.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  have hksInv : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ ks.symm ks.target := by
    exact M.symm.contDiff.contMDiff.comp_contMDiffOn
      (he.mono inter_subset_left)
  have hMr (x : E2) :
      (sN x).1 ^ 2 + (sN x).2 ^ 2 = rho ^ 2 * ‖x‖ ^ 2 := by
    dsimp [sN]
    calc
      (sigma * rho * (J2 x).2) ^ 2 + (sigma * rho * (J2 x).1) ^ 2 =
          sigma ^ 2 * rho ^ 2 * ((J2 x).1 ^ 2 + (J2 x).2 ^ 2) := by ring
      _ = rho ^ 2 * ‖x‖ ^ 2 := by rw [hsigmaSq, hJ2]; ring
  have hsurj : Function.Surjective sN := by
    intro s
    refine ⟨J2.symm (sigma / rho * s.2, sigma / rho * s.1), ?_⟩
    dsimp [sN]
    rw [J2.apply_symm_apply]
    apply Prod.ext <;> field_simp [hrho.ne'] <;> ring_nf <;> rw [hsigmaSq] <;> ring
  have hlt (x : E2) :
      (sN x).1 ^ 2 + (sN x).2 ^ 2 < rho ^ 2 ↔ ‖x‖ < 1 := by
    rw [hMr]
    simpa only [one_pow, mul_one] using
      ((mul_lt_mul_iff_right₀ (sq_pos_of_pos hrho) :
        rho ^ 2 * ‖x‖ ^ 2 < rho ^ 2 * (1 : ℝ) ^ 2 ↔ ‖x‖ ^ 2 < 1 ^ 2).trans
        (sq_lt_sq₀ (norm_nonneg x) zero_le_one))
  have hle (x : E2) :
      (sN x).1 ^ 2 + (sN x).2 ^ 2 ≤ rho ^ 2 ↔ ‖x‖ ≤ 1 := by
    rw [hMr]
    simpa only [one_pow, mul_one] using
      ((mul_le_mul_iff_right₀ (sq_pos_of_pos hrho) :
        rho ^ 2 * ‖x‖ ^ 2 ≤ rho ^ 2 * (1 : ℝ) ^ 2 ↔ ‖x‖ ^ 2 ≤ 1 ^ 2).trans
        (sq_le_sq₀ (norm_nonneg x) zero_le_one))
  have himage (S : Set E2) (U : Set (ℝ × ℝ))
      (hSU : ∀ x : E2, x ∈ S ↔ sN x ∈ U) : sN '' S = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hSU x).mp hx
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, (hSU x).mpr hy, rfl⟩
  have hopen : sN '' ball (0 : E2) 1 =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} := by
    exact himage _ _ (fun x => by
      simpa only [mem_ball_zero_iff, mem_ofPred_eq] using (hlt x).symm)
  have hclosed : sN '' closedBall (0 : E2) 1 =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} := by
    exact himage _ _ (fun x => by
      simpa only [mem_closedBall_zero_iff, mem_ofPred_eq] using (hle x).symm)
  have hbuffer2 : closedBall (0 : E2) 2 ⊆ ks.source := by
    rw [hsource]
    intro x hx
    apply hbuffer
    change (sN x).1 ^ 2 + (sN x).2 ^ 2 ≤ (2 * rho) ^ 2
    rw [hMr]
    have hn := mem_closedBall_zero_iff.mp hx
    have hn2 : ‖x‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg x]
    nlinarith [sq_pos_of_pos hrho]
  refine ⟨ks, hsource, htarget, (fun _ => rfl), (fun _ => rfl), hbuffer2, hks,
    hksInv, ?_, ?_, ?_⟩
  · have hfun : (ks : E2 → UnitTwoSphere) = e.symm ∘ sN := by
      funext x
      rfl
    rw [hfun, image_comp, hopen]
  · have hfun : (ks : E2 → UnitTwoSphere) = e.symm ∘ sN := by
      funext x
      rfl
    rw [hfun, image_comp, hclosed]
  · intro z r i
    change e.symm (sN (J2.symm
      (sx i * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2),
        sy i * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2)))) = _
    have hscale (v : ℝ) : Real.sqrt (rho ^ 2 * v) = rho * Real.sqrt v := by
      rw [Real.sqrt_mul (sq_nonneg rho), Real.sqrt_sq hrho.le]
    have hplus : (rho ^ 2 * r ^ 2 + z) / 2 =
        rho ^ 2 * ((r ^ 2 + z / rho ^ 2) / 2) := by
      field_simp [hrho.ne']
    have hminus : (rho ^ 2 * r ^ 2 - z) / 2 =
        rho ^ 2 * ((r ^ 2 - z / rho ^ 2) / 2) := by
      field_simp [hrho.ne']
    have hp : rho * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2) =
        Real.sqrt ((rho ^ 2 * r ^ 2 + z) / 2) := by rw [hplus, hscale]
    have hm : rho * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2) =
        Real.sqrt ((rho ^ 2 * r ^ 2 - z) / 2) := by rw [hminus, hscale]
    apply congrArg e.symm
    dsimp [sN]
    rw [J2.apply_symm_apply]
    apply Prod.ext
    · change sigma * rho * (sy i * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2)) =
        sigma * (sy i * Real.sqrt ((rho ^ 2 * r ^ 2 - z) / 2))
      calc
        sigma * rho * (sy i * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2)) =
            sigma * sy i * (rho * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2)) := by ring
        _ = sigma * (sy i * Real.sqrt ((rho ^ 2 * r ^ 2 - z) / 2)) := by
          rw [hm]
          ring
    · change sigma * rho * (sx i * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2)) =
        sigma * (sx i * Real.sqrt ((rho ^ 2 * r ^ 2 + z) / 2))
      calc
        sigma * rho * (sx i * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2)) =
            sigma * sx i * (rho * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2)) := by ring
        _ = sigma * (sx i * Real.sqrt ((rho ^ 2 * r ^ 2 + z) / 2)) := by
          rw [hp]
          ring

end PoincareConjecture.M25.Topology3D
