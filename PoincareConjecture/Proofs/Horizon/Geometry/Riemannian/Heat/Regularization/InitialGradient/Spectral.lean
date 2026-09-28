import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.ResolventPowers
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.EnergyFlow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}


def EnergyTest.negLaplacianTest (φ : EnergyTest D Ω) : EnergyTest D Ω :=
  φ.oneSubLaplacianTest - φ

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
@[simp] theorem EnergyTest.negLaplacianTest_apply (φ : EnergyTest D Ω) (x : M) :
    φ.negLaplacianTest x = -D.laplacian φ x := by
  change (φ x - D.laplacian φ x) - φ x = _
  ring

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in
theorem EnergyTest.iterate_negLaplacianTest_apply (φ : EnergyTest D Ω) (j : ℕ) (x : M) :
    ((EnergyTest.negLaplacianTest)^[j] φ) x =
      (-1 : ℝ) ^ j * ((D.laplacian)^[j] (φ : M → ℝ)) x := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', EnergyTest.negLaplacianTest_apply,
      show (((EnergyTest.negLaplacianTest)^[j] φ) : M → ℝ) =
        (fun y => (-1 : ℝ) ^ j * ((D.laplacian)^[j] (φ : M → ℝ)) y) from funext ih,
      D.laplacian_const_mul, Function.iterate_succ_apply', pow_succ]
    ring

theorem EnergyTest.norm_toDomainL2_iterate_negLaplacianTest
    (hΩ : IsOpen Ω) (φ : EnergyTest D Ω) (j : ℕ) :
    ‖toDomainL2 D Ω (((EnergyTest.negLaplacianTest)^[j]) φ : H1Zero D Ω)‖ =
      (eLpNorm ((D.laplacian)^[j] (φ : M → ℝ)) 2 g.volumeMeasure).toReal := by
  rw [norm_toDomainL2 hΩ.measurableSet, toL2_coe]
  change ‖(((EnergyTest.negLaplacianTest)^[j]) φ).memLp.toLp
    (((EnergyTest.negLaplacianTest)^[j]) φ)‖ = _
  rw [Lp.norm_def, eLpNorm_congr_ae (((EnergyTest.negLaplacianTest)^[j]) φ).memLp.coeFn_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [] with x
  rw [EnergyTest.iterate_negLaplacianTest_apply]
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem EnergyTest.repr_negLaplacianTest
    (hn : 0 < n) (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (φ : EnergyTest D Ω) (i : EigenIndex D Ω) :
    (eigenbasis D Ω hn hΩ hc).repr
        (toDomainL2 D Ω (φ.negLaplacianTest : H1Zero D Ω)) i =
      eigenvalue D Ω i * (eigenbasis D Ω hn hΩ hc).repr
        (toDomainL2 D Ω (φ : H1Zero D Ω)) i := by
  have h := congrArg (fun f => (eigenbasis D Ω hn hΩ hc).repr f i)
    (domainL2Resolvent_oneSubLaplacianTest hΩ φ)
  rw [domainL2Resolvent_repr] at h
  have he := resolvent_eigenvalue_mul_one_add D Ω i
  have h' : (1 + eigenvalue D Ω i) * (eigenbasis D Ω hn hΩ hc).repr
      (toDomainL2 D Ω (φ : H1Zero D Ω)) i = (eigenbasis D Ω hn hΩ hc).repr
      (toDomainL2 D Ω (φ.oneSubLaplacianTest : H1Zero D Ω)) i := by
    rw [← h, ← mul_assoc, mul_comm (1 + eigenvalue D Ω i), he, one_mul]
  simp only [EnergyTest.negLaplacianTest, UniformSpace.Completion.coe_sub,
    map_sub, lp.coeFn_sub, Pi.sub_apply]
  linarith only [h']


theorem norm_heatSemigroup_test_sub_le
    (hn : 0 < n) (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (φ : EnergyTest D Ω) (t : ℝ≥0) :
    ‖heatSemigroup D Ω hn hΩ hc t (toDomainL2 D Ω (φ : H1Zero D Ω)) -
        toDomainL2 D Ω (φ : H1Zero D Ω)‖ ≤
      (t : ℝ) * ‖toDomainL2 D Ω (φ.negLaplacianTest : H1Zero D Ω)‖ := by
  let b := eigenbasis D Ω hn hΩ hc
  let f := toDomainL2 D Ω (φ : H1Zero D Ω)
  let w := toDomainL2 D Ω (φ.negLaplacianTest : H1Zero D Ω)
  have hnorm : ‖b.repr (heatSemigroup D Ω hn hΩ hc t f - f)‖ ≤
      ‖(t : ℝ) • b.repr w‖ := by
    apply lp.norm_mono (by norm_num)
    intro i
    have hrate := eigenvalue_nonneg D Ω hn hΩ hc i
    have hexp : Real.exp (-eigenvalue D Ω i * (t : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrate) t.coe_nonneg)
    have hbound : |Real.exp (-eigenvalue D Ω i * (t : ℝ)) - 1| ≤
        (t : ℝ) * eigenvalue D Ω i := by
      rw [abs_of_nonpos (sub_nonpos.mpr hexp)]
      have := Real.add_one_le_exp (-eigenvalue D Ω i * (t : ℝ))
      nlinarith
    have heq : b.repr (heatSemigroup D Ω hn hΩ hc t f) i =
        Real.exp (-eigenvalue D Ω i * (t : ℝ)) * b.repr f i :=
      Poincare.Analysis.Dirichlet.Spectral.heat_repr _ _ _ _ _
    simp only [map_sub, lp.coeFn_sub, Pi.sub_apply, heq, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul]
    change |Real.exp (-eigenvalue D Ω i * (t : ℝ)) * b.repr f i - b.repr f i| ≤
      |(t : ℝ) * b.repr w i|
    rw [← sub_one_mul, abs_mul, show b.repr w i = eigenvalue D Ω i * b.repr f i
      from φ.repr_negLaplacianTest hn hΩ hc i, abs_mul, abs_mul,
      abs_of_nonneg t.coe_nonneg, abs_of_nonneg hrate, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
  simpa only [b.repr.norm_map, norm_smul, Real.norm_of_nonneg t.coe_nonneg] using hnorm

theorem heatSpectralPower_test_eq_heatSemigroup_iterate
    (hn : 0 < n) (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (φ : EnergyTest D Ω) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    heatSpectralPower D Ω hn hΩ hc j t (toDomainL2 D Ω (φ : H1Zero D Ω)) =
      heatSemigroup D Ω hn hΩ hc t.toNNReal
        (toDomainL2 D Ω (((EnergyTest.negLaplacianTest)^[j]) φ : H1Zero D Ω)) := by
  have hrepr (k : ℕ) (i : EigenIndex D Ω) :
      (eigenbasis D Ω hn hΩ hc).repr
          (toDomainL2 D Ω (((EnergyTest.negLaplacianTest)^[k]) φ : H1Zero D Ω)) i =
        eigenvalue D Ω i ^ k * (eigenbasis D Ω hn hΩ hc).repr
          (toDomainL2 D Ω (φ : H1Zero D Ω)) i := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', EnergyTest.repr_negLaplacianTest hn hΩ hc, ih,
        pow_succ]
      ring
  apply (eigenbasis D Ω hn hΩ hc).repr.injective
  ext i
  rw [heatSpectralPower_repr D Ω hn hΩ hc j ht]
  simp only [heatSemigroup, Poincare.Analysis.Dirichlet.Spectral.heat_repr,
    Real.coe_toNNReal _ ht.le, hrepr]
  change eigenvalue D Ω i ^ j * Real.exp (-eigenvalue D Ω i * t) * _ =
    Real.exp (-eigenvalue D Ω i * t) * (eigenvalue D Ω i ^ j * _)
  ring

end PoincareConjecture.LeviCivitaData.Dirichlet
