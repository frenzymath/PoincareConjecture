import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.EnergyBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients









noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



lemma divergenceCoefficients_refl_eq_energy (D : LeviCivitaData g)
    (x v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, divergenceCoefficients g
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))) x i j * v j * v i) =
      g.pullbackVolumeDensity id x * g.inner x
        (D.gradient (innerSL ℝ v) x) (D.gradient (innerSL ℝ v) x) := by
  let e := OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))
  have heq : (e : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = id := rfl
  have hb : g.pullbackCoefficients e x = g.euclideanCoefficients x := by
    ext u w
    simp [RiemannianMetric.pullbackCoefficients, heq]
    rfl
  have hderiv : mvfderiv (𝓡 n) (innerSL ℝ v) x = innerSL ℝ v := by
    ext u
    simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  have hg : D.gradient (innerSL ℝ v) x =
      (g.euclideanCoefficients x).inverse (innerSL ℝ v) := by
    unfold LeviCivitaData.gradient
    rw [hderiv]
    rfl
  have hdual : g.inner x (D.gradient (innerSL ℝ v) x) (D.gradient (innerSL ℝ v) x) =
      inner ℝ v ((g.euclideanCoefficients x).inverse (innerSL ℝ v)) := by
    rw [D.inner_gradient, hderiv, hg]
    rfl
  have h := sum_divergenceCoefficients_eq_inverse_pairing (g := g) e x
    (innerSL ℝ v) (innerSL ℝ v)
  rw [hb] at h
  simpa only [innerSL_apply_apply, EuclideanSpace.inner_single_right, starRingEnd_apply,
    star_trivial, one_mul, heq, hdual] using h



theorem divergenceCoefficients_refl_bounds (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    (Real.sqrt (a ^ n) / b) * ‖v‖ ^ 2 ≤
      ∑ i, ∑ j, divergenceCoefficients g
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))) x i j * v j * v i ∧
    (∑ i, ∑ j, divergenceCoefficients g
        (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))) x i j * v j * v i) ≤
      (Real.sqrt (b ^ n) / a) * ‖v‖ ^ 2 := by
  rw [divergenceCoefficients_refl_eq_energy D]
  have hlow := fderiv_sq_le_gradient_energy D (innerSL ℝ v) x hb.le
    (fun w => (hell w).2)
  have hupp := gradient_energy_le_fderiv_sq D (innerSL ℝ v) x ha
    (fun w => (hell w).1)
  simp only [ContinuousLinearMap.fderiv, innerSL_apply_norm] at hlow hupp
  have hlow' : ‖v‖ ^ 2 / b ≤ g.inner x
      (D.gradient (innerSL ℝ v) x) (D.gradient (innerSL ℝ v) x) := by
    apply (div_le_iff₀ hb).mpr
    simpa only [mul_comm] using hlow
  obtain ⟨hdlo, hdup⟩ := g.pullbackVolumeDensity_id_bounds x ha hell
  have hdpos : 0 ≤ g.pullbackVolumeDensity id x :=
    (Real.sqrt_nonneg _).trans hdlo
  constructor
  · calc
      _ = Real.sqrt (a ^ n) * (‖v‖ ^ 2 / b) := by ring
      _ ≤ _ := mul_le_mul hdlo hlow' (by positivity) hdpos
  · calc
      _ ≤ Real.sqrt (b ^ n) * (‖v‖ ^ 2 / a) :=
        mul_le_mul hdup hupp ((div_nonneg (sq_nonneg _) hb.le).trans hlow')
          (Real.sqrt_nonneg _)
      _ = _ := by ring

end PoincareConjecture.HarmonicCoordinates
