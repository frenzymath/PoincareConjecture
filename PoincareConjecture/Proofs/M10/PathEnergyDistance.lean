import PoincareConjecture.Proofs.M10.CurveEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M10


theorem integral_sqrt_le_sqrt_energy {a b : ℝ} (hab : a ≤ b) {E : ℝ → ℝ}
    (hE : ContinuousOn E (Icc a b)) (hpos : ∀ s, 0 ≤ E s) :
    (∫ s in Icc a b, Real.sqrt (E s)) ≤
      Real.sqrt ((b - a) * ∫ s in a..b, E s) := by
  have hv := hE.sqrt
  have hvint := hv.integrableOn_Icc (μ := volume)
  have hLp : MemLp (fun s ↦ Real.sqrt (E s)) 2 (volume.restrict (Icc a b)) :=
    (memLp_two_iff_integrable_sq hvint.aestronglyMeasurable).mpr
      ((hv.pow 2).integrableOn_Icc)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall (fun s ↦ Real.sqrt_nonneg (E s)))
    (Eventually.of_forall (fun _ : ℝ ↦ (zero_le_one : (0 : ℝ) ≤ 1)))
    (by simpa using hLp) (memLp_const (1 : ℝ))
  simp only [mul_one, Real.rpow_two, Real.sq_sqrt (hpos _), one_pow,
    ← Real.sqrt_eq_rpow] at hCS
  have hmeasure : (∫ _ : ℝ in Icc a b, (1 : ℝ)) = b - a := by
    simp [sub_nonneg.mpr hab]
  rw [hmeasure, mul_comm, ← Real.sqrt_mul (sub_nonneg.mpr hab)] at hCS
  simpa only [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab] using hCS

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem edist_le_sqrt_curve_energy (g : RiemannianMetric n M)
    {γ : ℝ → M} {U : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ U)
    (hab : a ≤ b) (hI : Icc a b ⊆ U) :
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal
      (Real.sqrt ((b - a) * ∫ s in a..b,
        g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := fun s ↦ g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s)
  have hE : ContinuousOn E (Icc a b) :=
    (curve_energy_continuousOn g hU hγ).mono hI
  have hpos (s : ℝ) : 0 ≤ E s := by
    by_cases hv : curveVelocity (n := n) γ s = 0
    · simp [E, hv]
    · exact (g.pos _ _ hv).le
  have hlength : Manifold.pathELength (𝓡 n) γ a b =
      ENNReal.ofReal (∫ s in Icc a b, Real.sqrt (E s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
      ofReal_integral_eq_lintegral_ofReal hE.sqrt.integrableOn_Icc
        (Eventually.of_forall (fun s ↦ Real.sqrt_nonneg (E s)))]
    apply lintegral_congr
    intro s
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  change Manifold.riemannianEDist (𝓡 n) (γ a) (γ b) ≤ _
  apply (Manifold.riemannianEDist_le_pathELength (hγ.mono hI) rfl rfl hab).trans
  rw [hlength]
  exact ENNReal.ofReal_le_ofReal (integral_sqrt_le_sqrt_energy hab hE hpos)

end PoincareConjecture.M10
