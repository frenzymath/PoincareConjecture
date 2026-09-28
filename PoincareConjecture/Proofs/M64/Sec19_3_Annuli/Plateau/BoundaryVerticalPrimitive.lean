import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseFlux
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)





def m64VerticalPrimitive (f : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  ∫ s in p 1..1, f (annulusPoint (p 0) s)





theorem m64VerticalPrimitive_contDiff {f : LoopPlane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (m64VerticalPrimitive f) := by
  let F : LoopPlane × ℝ → ℝ := fun q =>
    f (annulusPoint (q.1 0) (q.1 1 + (1 - q.1 1) * q.2))
  have hF : ContDiff ℝ ∞ F := by
    apply hf.comp
    have heq : (fun q : LoopPlane × ℝ =>
        annulusPoint (q.1 0) (q.1 1 + (1 - q.1 1) * q.2)) =
        fun q => q.1 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
          (q.1 1 + (1 - q.1 1) * q.2) • e1 := by
      funext q
      ext i
      fin_cases i <;> simp [annulusPoint]
    rw [heq]
    have h0 : ContDiff ℝ ∞ (fun q : LoopPlane × ℝ => q.1 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_fst
    have h1 : ContDiff ℝ ∞ (fun q : LoopPlane × ℝ => q.1 1) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_fst
    exact (h0.smul contDiff_const).add
      ((h1.add ((contDiff_const.sub h1).mul contDiff_snd)).smul contDiff_const)
  have hh := Poincare.Analysis.contDiff_parameter_intervalIntegral_of_contDiff hF 0 1
  have heq : m64VerticalPrimitive f = fun p : LoopPlane =>
      (1 - p 1) * ∫ s in (0 : ℝ)..1, F (p, s) := by
    funext p
    symm
    simpa only [F, m64VerticalPrimitive, smul_eq_mul, mul_zero, add_zero, mul_one,
      add_sub_cancel] using
      intervalIntegral.smul_integral_comp_add_mul
        (fun s => f (annulusPoint (p 0) s)) (1 - p 1) (p 1)
        (a := 0) (b := 1)
  rw [heq]
  exact (contDiff_const.sub (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff).mul hh





theorem m64VerticalPrimitive_top (f : LoopPlane → ℝ) (x : ℝ) :
    m64VerticalPrimitive f (annulusPoint x 1) = 0 := by
  simp [m64VerticalPrimitive, annulusPoint]





theorem m64VerticalPrimitive_vertical_derivative {f : LoopPlane → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : LoopPlane) :
    fderiv ℝ (m64VerticalPrimitive f) p e1 = -f p := by
  have hc : Continuous (fun s => f (annulusPoint (p 0) s)) :=
    hf.continuous.comp (by unfold annulusPoint; fun_prop)
  have hd := intervalIntegral.integral_hasDerivAt_left
    (hc.intervalIntegrable (p 1) 1) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt
  have hcomp := ((m64VerticalPrimitive_contDiff hf).differentiable (by simp)
    (annulusPoint (p 0) (p 1))).hasFDerivAt.comp_hasDerivAt (p 1)
      (m64AnnulusPoint_vertical_hasDerivAt (p 0) (p 1))
  have heq : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hfun : (fun s => m64VerticalPrimitive f (annulusPoint (p 0) s)) =
      fun s => ∫ t in s..1, f (annulusPoint (p 0) t) := by
    funext s
    simp only [m64VerticalPrimitive, annulusPoint, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change HasDerivAt (fun s => m64VerticalPrimitive f (annulusPoint (p 0) s)) _ _ at hcomp
  rw [hfun] at hcomp
  simpa only [heq] using hcomp.unique hd





theorem m64VerticalPrimitive_sq_le_slice {f : LoopPlane → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (m64VerticalPrimitive f (annulusPoint x s)) ^ 2 ≤
      ∫ t in Icc (0 : ℝ) 1, (f (annulusPoint x t)) ^ 2 := by
  have hc : Continuous (fun t => f (annulusPoint x t)) :=
    hf.continuous.comp (by unfold annulusPoint; fun_prop)
  have hi : MemLp (fun t => f (annulusPoint x t)) 2 (volume.restrict (Icc s 1)) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
      (hc.pow 2).integrableOn_Icc
  have hsq := M64Uniformization.scalar_integral_mul_sq_le
    (f := fun _ : ℝ => (1 : ℝ)) (memLp_const (1 : ℝ)) hi
  simp only [one_mul, one_pow, setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Icc_of_le hs.2] at hsq
  have hsmall : (∫ t in Icc s 1, (f (annulusPoint x t)) ^ 2) ≤
      ∫ t in Icc (0 : ℝ) 1, (f (annulusPoint x t)) ^ 2 :=
    setIntegral_mono_set (hc.pow 2).integrableOn_Icc
      (ae_of_all _ (fun _ => sq_nonneg _))
      (ae_of_all _ (fun _ ht => ⟨hs.1.trans ht.1, ht.2⟩))
  have hbound : (1 - s) * (∫ t in Icc s 1, (f (annulusPoint x t)) ^ 2) ≤
      ∫ t in Icc (0 : ℝ) 1, (f (annulusPoint x t)) ^ 2 := by
    calc
      _ ≤ 1 * (∫ t in Icc s 1, (f (annulusPoint x t)) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith [hs.1])
          (integral_nonneg (fun _ => sq_nonneg _))
      _ ≤ _ := by simpa only [one_mul] using hsmall
  have heq : m64VerticalPrimitive f (annulusPoint x s) =
      ∫ t in Icc s 1, f (annulusPoint x t) := by
    change (∫ t in s..1, f (annulusPoint x t)) = _
    rw [intervalIntegral.integral_of_le hs.2, ← integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hsq.trans hbound





theorem m64VerticalPrimitive_l2_bounds {f : LoopPlane → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    (∫ p in S, (m64VerticalPrimitive f p) ^ 2) ≤ (∫ p in S, (f p) ^ 2) ∧
      (∫ x in Icc (0 : ℝ) curvePeriod,
        (m64VerticalPrimitive f (annulusPoint x 0)) ^ 2) ≤ (∫ p in S, (f p) ^ 2) := by
  let phi := m64VerticalPrimitive f
  have hphi : Continuous phi := (m64VerticalPrimitive_contDiff hf).continuous
  have hF : Integrable (fun q : ℝ × ℝ => (f (annulusPoint q.1 q.2)) ^ 2)
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (fun q : ℝ × ℝ => (f (annulusPoint q.1 q.2)) ^ 2) :=
      (hf.continuous.comp (by unfold annulusPoint; fun_prop)).pow 2
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hG : Integrable (fun q : ℝ × ℝ => (phi (annulusPoint q.1 q.2)) ^ 2)
      ((volume.restrict (Icc (0 : ℝ) curvePeriod)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hc : Continuous (fun q : ℝ × ℝ => (phi (annulusPoint q.1 q.2)) ^ 2) :=
      (hphi.comp (by unfold annulusPoint; fun_prop)).pow 2
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hpoint (x : ℝ) :
      (∫ s in Icc (0 : ℝ) 1, (phi (annulusPoint x s)) ^ 2) ≤
        ∫ s in Icc (0 : ℝ) 1, (f (annulusPoint x s)) ^ 2 := by
    have hc : Continuous (fun s => phi (annulusPoint x s)) :=
      hphi.comp (by unfold annulusPoint; fun_prop)
    have hh := setIntegral_mono_on (hc.pow 2).integrableOn_Icc
      (integrableOn_const (μ := volume)
        (C := ∫ t in Icc (0 : ℝ) 1, (f (annulusPoint x t)) ^ 2)
        isCompact_Icc.measure_ne_top)
      measurableSet_Icc (fun s hs => m64VerticalPrimitive_sq_le_slice hf x hs)
    simpa only [Pi.pow_apply, setIntegral_const, Real.volume_real_Icc, sub_zero,
      max_eq_left zero_le_one, smul_eq_mul, one_mul] using hh
  constructor
  · change (∫ p in S, (phi p) ^ 2) ≤ (∫ p in S, (f p) ^ 2)
    rw [m64AnnulusInteriorIntegral_eq_iterated (fun p => (phi p) ^ 2) (hphi.pow 2),
      m64AnnulusInteriorIntegral_eq_iterated (fun p => (f p) ^ 2) (hf.continuous.pow 2)]
    exact integral_mono hG.integral_prod_left hF.integral_prod_left hpoint
  · rw [m64AnnulusInteriorIntegral_eq_iterated (fun p => (f p) ^ 2) (hf.continuous.pow 2)]
    have hc : Continuous (fun x => (phi (annulusPoint x 0)) ^ 2) :=
      (hphi.comp (by unfold annulusPoint; fun_prop)).pow 2
    exact integral_mono hc.integrableOn_Icc hF.integral_prod_left
      (fun x => m64VerticalPrimitive_sq_le_slice hf x ⟨le_rfl, zero_le_one⟩)

end PoincareConjecture
