import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem saddle_selected_source_geometry
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (D : SaddlePieceData psi u) (rho : ℝ) (hrho : 0 < rho)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2)
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hks : ∀ x : E2, ks x = D.morse.symm (N (rho • J2 x))) :
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    ks '' ball (0 : E2) 1 =
      D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < rho ^ 2} ∧
    ks '' closedBall (0 : E2) 1 =
      D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ∧
    (∀ (z r : ℝ) (i : Fin 4),
      ks (J2.symm
        (sx i * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2),
          sy i * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2))) =
        D.morse.symm (N
          (sx i * Real.sqrt ((rho ^ 2 * r ^ 2 + z) / 2),
            sy i * Real.sqrt ((rho ^ 2 * r ^ 2 - z) / 2)))) := by
  let M : E2 → ℝ × ℝ := fun x => N (rho • J2 x)
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hsurj : Surjective M := by
    intro s
    refine ⟨J2.symm (rho⁻¹ • N.symm s), ?_⟩
    dsimp only [M]
    rw [J2.apply_symm_apply, smul_inv_smul₀ hrho.ne', N.apply_symm_apply]
  have hMr (x : E2) : r2 (M x) = rho ^ 2 * ‖x‖ ^ 2 := by
    calc
      r2 (M x) = rho ^ 2 * ((J2 x).1 ^ 2 + (J2 x).2 ^ 2) := by
        change (N (rho • J2 x)).1 ^ 2 + (N (rho • J2 x)).2 ^ 2 = _
        rw [hN]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      _ = rho ^ 2 * ‖x‖ ^ 2 := by rw [hJ2]
  have hlt (x : E2) : r2 (M x) < rho ^ 2 ↔ ‖x‖ < 1 := by
    rw [hMr]
    simpa only [one_pow, mul_one] using
      ((mul_lt_mul_iff_right₀ hrho2 :
        rho ^ 2 * ‖x‖ ^ 2 < rho ^ 2 * (1 : ℝ) ^ 2 ↔ ‖x‖ ^ 2 < 1 ^ 2).trans
        (sq_lt_sq₀ (norm_nonneg x) zero_le_one))
  have hle (x : E2) : r2 (M x) ≤ rho ^ 2 ↔ ‖x‖ ≤ 1 := by
    rw [hMr]
    simpa only [one_pow, mul_one] using
      ((mul_le_mul_iff_right₀ hrho2 :
        rho ^ 2 * ‖x‖ ^ 2 ≤ rho ^ 2 * (1 : ℝ) ^ 2 ↔ ‖x‖ ^ 2 ≤ 1 ^ 2).trans
        (sq_le_sq₀ (norm_nonneg x) zero_le_one))
  have himage (s : Set E2) (t : Set (ℝ × ℝ))
      (hst : ∀ x : E2, x ∈ s ↔ M x ∈ t) : M '' s = t := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hst x).mp hx
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, (hst x).mpr hy, rfl⟩
  have hopen : M '' ball (0 : E2) 1 = {s | r2 s < rho ^ 2} :=
    himage _ _ (fun x => by
      simpa only [mem_ball_zero_iff, mem_ofPred_eq] using (hlt x).symm)
  have hclosed : M '' closedBall (0 : E2) 1 = {s | r2 s ≤ rho ^ 2} :=
    himage _ _ (fun x => by
      simpa only [mem_closedBall_zero_iff, mem_ofPred_eq] using (hle x).symm)
  have hfun : (ks : E2 → UnitTwoSphere) = D.morse.symm ∘ M := funext hks
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun, image_comp, hopen]
  · rw [hfun, image_comp, hclosed]
  · intro z r i
    have hscale (v : ℝ) : Real.sqrt (rho ^ 2 * v) = rho * Real.sqrt v := by
      rw [Real.sqrt_mul (sq_nonneg rho), Real.sqrt_sq hrho.le]
    have hplus : (rho ^ 2 * r ^ 2 + z) / 2 =
        rho ^ 2 * ((r ^ 2 + z / rho ^ 2) / 2) := by
      field_simp
    have hminus : (rho ^ 2 * r ^ 2 - z) / 2 =
        rho ^ 2 * ((r ^ 2 - z / rho ^ 2) / 2) := by
      field_simp
    have hp : rho * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2) =
        Real.sqrt ((rho ^ 2 * r ^ 2 + z) / 2) := by rw [hplus, hscale]
    have hm : rho * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2) =
        Real.sqrt ((rho ^ 2 * r ^ 2 - z) / 2) := by rw [hminus, hscale]
    rw [hks, J2.apply_symm_apply]
    apply congrArg D.morse.symm
    apply congrArg N
    apply Prod.ext
    · change rho * (_ * Real.sqrt ((r ^ 2 + z / rho ^ 2) / 2)) = _
      rw [mul_left_comm, hp]
    · change rho * (_ * Real.sqrt ((r ^ 2 - z / rho ^ 2) / 2)) = _
      rw [mul_left_comm, hm]

end PoincareConjecture.M25.Topology3D
