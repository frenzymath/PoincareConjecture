import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakReplacement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Inclusion









noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 12

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω₁ Ω₂ : Set M}


@[simp] theorem gradientEnergy_inclusion (hΩ : Ω₁ ⊆ Ω₂) (v w : H1Zero D Ω₁) :
    gradientEnergy D Ω₂ (inclusion hΩ v) (inclusion hΩ w) =
      gradientEnergy D Ω₁ v w := by
  simp only [gradientEnergy_apply, inner_inclusion, toL2_inclusion]


theorem gradientEnergy_test_inclusion [PreconnectedSpace M]
    (hΩ : Ω₁ ⊆ Ω₂) (q : EnergyTest D Ω₂) (v : H1Zero D Ω₁) :
    gradientEnergy D Ω₂ (q : H1Zero D Ω₂) (inclusion hΩ v) =
      -⟪q.laplacianLp, toL2 D Ω₁ v⟫_ℝ := by
  rw [gradientEnergy_symm, gradientEnergy_eq_neg_inner_laplacianLp,
    toL2_inclusion, real_inner_comm]


theorem weakPoisson_gradientEnergy_orthogonal [PreconnectedSpace M]
    (hΩ : Ω₁ ⊆ Ω₂) {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω₁ P)
    (q : EnergyTest D Ω₂) (v : H1Zero D Ω₁) :
    gradientEnergy D Ω₂
      ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp))
      (inclusion hΩ v) = 0 := by
  simp only [map_add, add_apply, gradientEnergy_test_inclusion,
    gradientEnergy_inclusion, weakPoisson_spec, neg_add_cancel]



theorem weakPoisson_gradientEnergy_pythagorean [PreconnectedSpace M]
    (hΩ : Ω₁ ⊆ Ω₂) {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω₁ P)
    (q : EnergyTest D Ω₂) (v : H1Zero D Ω₁) :
    gradientEnergy D Ω₂ ((q : H1Zero D Ω₂) + inclusion hΩ v)
        ((q : H1Zero D Ω₂) + inclusion hΩ v) =
      gradientEnergy D Ω₂
          ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp))
          ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp)) +
        gradientEnergy D Ω₁ (v - weakPoisson D Ω₁ hP0 hP q.laplacianLp)
          (v - weakPoisson D Ω₁ hP0 hP q.laplacianLp) := by
  let w := weakPoisson D Ω₁ hP0 hP q.laplacianLp
  let U : H1Zero D Ω₂ := q + inclusion hΩ w
  have horth : gradientEnergy D Ω₂ U (inclusion hΩ (v - w)) = 0 :=
    weakPoisson_gradientEnergy_orthogonal hΩ hP0 hP q (v - w)
  have horth' : gradientEnergy D Ω₂ (inclusion hΩ (v - w)) U = 0 := by
    rw [gradientEnergy_symm, horth]
  have heq : (q : H1Zero D Ω₂) + inclusion hΩ v = U + inclusion hΩ (v - w) := by
    dsimp [U]
    rw [map_sub]
    abel
  change _ = gradientEnergy D Ω₂ U U + gradientEnergy D Ω₁ (v - w) (v - w)
  rw [heq]
  simp only [map_add, add_apply, horth, horth', gradientEnergy_inclusion,
    add_zero, zero_add]


theorem weakPoisson_gradientEnergy_minimizes [PreconnectedSpace M]
    (hΩ : Ω₁ ⊆ Ω₂) {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω₁ P)
    (q : EnergyTest D Ω₂) (v : H1Zero D Ω₁) :
    gradientEnergy D Ω₂
        ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp))
        ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp)) ≤
      gradientEnergy D Ω₂ ((q : H1Zero D Ω₂) + inclusion hΩ v)
        ((q : H1Zero D Ω₂) + inclusion hΩ v) := by
  rw [weakPoisson_gradientEnergy_pythagorean hΩ hP0 hP q v]
  exact le_add_of_nonneg_right (gradientEnergy_self_nonneg _)


theorem weakPoisson_gradientEnergy_split [PreconnectedSpace M]
    (hΩ : Ω₁ ⊆ Ω₂) {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω₁ P)
    (q : EnergyTest D Ω₂) :
    gradientEnergy D Ω₂ (q : H1Zero D Ω₂) q =
      gradientEnergy D Ω₂
          ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp))
          ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp)) +
        gradientEnergy D Ω₁ (weakPoisson D Ω₁ hP0 hP q.laplacianLp)
          (weakPoisson D Ω₁ hP0 hP q.laplacianLp) := by
  simpa only [map_zero, add_zero, zero_sub, map_neg, neg_apply, neg_neg] using
    weakPoisson_gradientEnergy_pythagorean hΩ hP0 hP q 0


theorem weakPoisson_gradientEnergy_le [PreconnectedSpace M]
    (hΩ : Ω₁ ⊆ Ω₂) {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω₁ P)
    (q : EnergyTest D Ω₂) :
    gradientEnergy D Ω₁ (weakPoisson D Ω₁ hP0 hP q.laplacianLp)
        (weakPoisson D Ω₁ hP0 hP q.laplacianLp) ≤
      ∫ x, g.inner x (D.gradient q x) (D.gradient q x) ∂g.volumeMeasure := by
  rw [← gradientEnergy_coe, weakPoisson_gradientEnergy_split hΩ hP0 hP q]
  exact le_add_of_nonneg_left (gradientEnergy_self_nonneg _)


theorem weakPoisson_replacement_gradientEnergy_le [PreconnectedSpace M]
    (hΩ : Ω₁ ⊆ Ω₂) {P : ℝ} (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω₁ P)
    (q : EnergyTest D Ω₂) :
    gradientEnergy D Ω₂
        ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp))
        ((q : H1Zero D Ω₂) + inclusion hΩ (weakPoisson D Ω₁ hP0 hP q.laplacianLp)) ≤
      ∫ x, g.inner x (D.gradient q x) (D.gradient q x) ∂g.volumeMeasure := by
  simpa only [map_zero, add_zero, gradientEnergy_coe] using
    weakPoisson_gradientEnergy_minimizes hΩ hP0 hP q 0

end PoincareConjecture.LeviCivitaData.Dirichlet

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n]
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem exists_weakHarmonicReplacement_energy_on_ball (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R)
    (q : EnergyTest D (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ w : H1Zero D (Metric.ball 0 R),
      IsWeakHarmonicReplacement (testToL2 D Set.univ q) w ∧
      gradientEnergy D (Metric.ball 0 R) w w ≤
        ∫ x, g.inner x (D.gradient q x) (D.gradient q x) ∂g.volumeMeasure ∧
      gradientEnergy D Set.univ
          ((q : H1Zero D Set.univ) + inclusion (subset_univ _) w)
          ((q : H1Zero D Set.univ) + inclusion (subset_univ _) w) ≤
        ∫ x, g.inner x (D.gradient q x) (D.gradient q x) ∂g.volumeMeasure ∧
      ∀ v : H1Zero D (Metric.ball 0 R),
        gradientEnergy D Set.univ
            ((q : H1Zero D Set.univ) + inclusion (subset_univ _) v)
            ((q : H1Zero D Set.univ) + inclusion (subset_univ _) v) =
          gradientEnergy D Set.univ
              ((q : H1Zero D Set.univ) + inclusion (subset_univ _) w)
              ((q : H1Zero D Set.univ) + inclusion (subset_univ _) w) +
            gradientEnergy D (Metric.ball 0 R) (v - w) (v - w) := by
  obtain ⟨P, hP0, hP⟩ := exists_metric_poincare_on_ball g D hR
  exact ⟨weakPoisson D (Metric.ball 0 R) hP0 hP q.laplacianLp,
    weakPoisson_isWeakHarmonicReplacement hP0 hP q,
    weakPoisson_gradientEnergy_le (subset_univ _) hP0 hP q,
    weakPoisson_replacement_gradientEnergy_le (subset_univ _) hP0 hP q,
    weakPoisson_gradientEnergy_pythagorean (subset_univ _) hP0 hP q⟩

end PoincareConjecture.HarmonicCoordinates
