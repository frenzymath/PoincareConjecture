import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusPeriodicHarmonicMinimum

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture

private theorem phase_hessian_sub_linear {f : LoopPlane → ℝ} {p : LoopPlane}
    (hf : ContDiffAt ℝ ∞ f p) (B : LoopPlane →L[ℝ] ℝ) (v w : LoopPlane) :
    fderiv ℝ (fderiv ℝ (fun q => f q - B q)) p v w =
      fderiv ℝ (fderiv ℝ f) p v w := by
  have h := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => LoopPlane) ℝ =>
      T ![v, w]) (iteratedFDeriv_sub_apply (hf.of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞))
        (B.contDiff.contDiffAt : ContDiffAt ℝ 2 B p))
  simp only [sub_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  have hB : fderiv ℝ B = fun _ : LoopPlane => B := funext fun _ => B.fderiv
  rw [hB] at h
  simpa only [Pi.sub_def, fderiv_const_apply, zero_apply, sub_zero] using h

theorem m64PeriodicModulus_eq_affine_of_constant_boundary
    {r : ℝ} (hr : 0 < r) {f : LoopPlane → ℝ} {c : ℝ}
    (hc : ContinuousOn f m64AnnulusDomain)
    (hf : ContDiffOn ℝ ∞ f m64AnnulusOpenStrip)
    (heq : ∀ p ∈ m64AnnulusOpenStrip,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0)
    (hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = 0)
    (hupper : ∀ x, f (annulusPoint x 1) = c) :
    ∀ p, p 1 ∈ Icc (0 : ℝ) 1 → f p = c * p 1 := by
  let B : LoopPlane →L[ℝ] ℝ := c • EuclideanSpace.proj (1 : Fin 2)
  let u : LoopPlane → ℝ := fun p => f p - B p
  have huc : ContinuousOn u m64AnnulusDomain := hc.sub B.continuous.continuousOn
  have hu : ContDiffOn ℝ 2 u m64AnnulusOpenStrip :=
    (hf.of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞)).sub B.contDiff.contDiffOn
  have hueq (p : LoopPlane) (hp : p ∈ m64AnnulusOpenStrip) :
      r * fderiv ℝ (fderiv ℝ u) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ u) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
    have h := phase_hessian_sub_linear
      (hf.contDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds hp)) B
    change r * fderiv ℝ (fderiv ℝ (fun q => f q - B q)) p _ _ +
      r⁻¹ * fderiv ℝ (fderiv ℝ (fun q => f q - B q)) p _ _ = 0
    rw [h, h]
    exact heq p hp
  have hup (x s : ℝ) : u (annulusPoint (x + curvePeriod) s) = u (annulusPoint x s) := by
    change f (annulusPoint (x + curvePeriod) s) - c * s = f (annulusPoint x s) - c * s
    rw [hperiod]
  have hu0 (x : ℝ) : u (annulusPoint x 0) = 0 := by
    change f (annulusPoint x 0) - c * 0 = 0
    rw [hlower]
    ring
  have hu1 (x : ℝ) : u (annulusPoint x 1) = 0 := by
    change f (annulusPoint x 1) - c * 1 = 0
    rw [hupper]
    ring
  have hn := m64PeriodicModulus_nonneg_of_boundary_nonneg hr huc hu hueq hup
    (fun x _ => (hu0 x).symm ▸ le_rfl) (fun x _ => (hu1 x).symm ▸ le_rfl)
  have hneg := m64PeriodicModulus_nonneg_of_boundary_nonneg hr huc.neg hu.neg
    (by
      intro p hp
      have hd : fderiv ℝ (-u) = -fderiv ℝ u := funext fun _ => fderiv_neg
      rw [hd]
      simp only [fderiv_neg, neg_apply]
      linarith [hueq p hp])
    (fun x s => congrArg Neg.neg (hup x s))
    (fun x _ => by simp only [Pi.neg_apply, hu0, neg_zero]; exact le_rfl)
    (fun x _ => by simp only [Pi.neg_apply, hu1, neg_zero]; exact le_rfl)
  intro p hp
  by_cases h0 : p 1 = 0
  · have hp0 : p = annulusPoint (p 0) 0 := by ext i; fin_cases i <;> simp [annulusPoint, h0]
    rw [hp0, hlower]
    simp [annulusPoint]
  by_cases h1 : p 1 = 1
  · have hp1 : p = annulusPoint (p 0) 1 := by ext i; fin_cases i <;> simp [annulusPoint, h1]
    rw [hp1, hupper]
    simp [annulusPoint]
  have hpi : p ∈ m64AnnulusOpenStrip :=
    ⟨lt_of_le_of_ne hp.1 (Ne.symm h0), lt_of_le_of_ne hp.2 h1⟩
  have hzero : u p = 0 := le_antisymm (neg_nonneg.mp (hneg p hpi)) (hn p hpi)
  exact sub_eq_zero.mp hzero

end PoincareConjecture
