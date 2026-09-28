import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveOscillation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakCompactness













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]



theorem m64CourantLebesgue_cylinder_slice
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f →
      ∀ a b E : ℝ, a < b →
        (∫ t in Icc a b, ∫ x in Icc (0 : ℝ) curvePeriod,
          m60EnergyDensity g f (annulusPoint t x)) ≤ E →
        ∃ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) curvePeriod, ∀ y ∈ Icc (0 : ℝ) curvePeriod,
          ‖e (f (annulusPoint t x)) - e (f (annulusPoint t y))‖ ^ 2 ≤ C * E / (b - a) := by
  obtain ⟨A, hA0, hA⟩ := M60.exists_observed_derivative_energy_bound g e he
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  refine ⟨4 * curvePeriod * A, by positivity, ?_⟩
  intro f hf a b E hab hE
  let d := fun p => fderiv ℝ (e ∘ f) p (EuclideanSpace.single (1 : Fin 2) 1)
  let q := fun t => ∫ x in Icc (0 : ℝ) curvePeriod, ‖d (annulusPoint t x)‖ ^ 2
  let energy := fun t => ∫ x in Icc (0 : ℝ) curvePeriod,
    m60EnergyDensity g f (annulusPoint t x)
  have hu : ContDiff ℝ 1 (e ∘ f) := contMDiff_iff_contDiff.mp (he.comp hf)
  have hd : Continuous d := (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpoint : Continuous (fun p : ℝ × ℝ => annulusPoint p.1 p.2) := by
    unfold annulusPoint
    fun_prop
  have hq : Continuous q := continuous_parametric_integral_of_continuous
    ((hd.comp hpoint).norm.pow 2) isCompact_Icc
  have henergy : Continuous energy := continuous_parametric_integral_of_continuous
    (f := fun t x : ℝ => m60EnergyDensity g f (annulusPoint t x))
    ((m60EnergyDensity_continuous g hf).comp hpoint) isCompact_Icc
  have hqE (t : ℝ) : q t ≤ A * energy t := by
    have hat : Continuous (annulusPoint t) := by unfold annulusPoint; fun_prop
    have hdt : Continuous (fun x => ‖d (annulusPoint t x)‖ ^ 2) :=
      (hd.comp hat).norm.pow 2
    have het : Continuous (fun x => m60EnergyDensity g f (annulusPoint t x)) :=
      (m60EnergyDensity_continuous g hf).comp hat
    rw [← integral_const_mul]
    apply integral_mono hdt.integrableOn_Icc (het.integrableOn_Icc.const_mul A)
    intro x
    simpa only [EuclideanSpace.basisFun_apply] using hA f hf (annulusPoint t x) 1
  have hbound : (∫ t in Icc a b, q t) ≤ A * E := by
    calc
      _ ≤ ∫ t in Icc a b, A * energy t :=
        integral_mono hq.integrableOn_Icc (henergy.integrableOn_Icc.const_mul A) hqE
      _ = A * ∫ t in Icc a b, energy t := integral_const_mul _ _
      _ ≤ A * E := mul_le_mul_of_nonneg_left hE hA0
  obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hq.continuousOn
  have hminint : (b - a) * q t ≤ ∫ s in Icc a b, q s := by
    have hconst : IntegrableOn (fun _ : ℝ => q t) (Icc a b) volume :=
      integrableOn_const isCompact_Icc.measure_ne_top
    have hh := setIntegral_mono_on hconst
      hq.integrableOn_Icc measurableSet_Icc (fun s hs => hmin hs)
    simpa only [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hab.le] using hh
  have hqt : q t ≤ A * E / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
    nlinarith
  refine ⟨t, ht, ?_⟩
  intro x hx y hy
  have hcurve (z : ℝ) : HasDerivAt (fun x => e (f (annulusPoint t x)))
      (d (annulusPoint t z)) z :=
    (hu.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt z
      (m64AnnulusPoint_vertical_hasDerivAt t z)
  have hosc := m64Curve_oscillation_sq_le
    (fun x => e (f (annulusPoint t x))) (fun x => d (annulusPoint t x))
    (hd.comp (show Continuous (annulusPoint t) by unfold annulusPoint; fun_prop))
    hcurve hx hy
  exact hosc.trans ((mul_le_mul_of_nonneg_left hqt (by positivity)).trans_eq (by ring))

end PoincareConjecture
