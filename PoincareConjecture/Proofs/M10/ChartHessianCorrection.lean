import PoincareConjecture.Proofs.M10.ChartMetricDual

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem fixedChart_second_fderiv_eq (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} (q₀ : M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f ((extChartAt (𝓡 n) q₀).symm y))
    (v : EuclideanSpace ℝ (Fin n)) :
    let e := extChartAt (𝓡 n) q₀
    let B := pullbackMetricForm g e.symm
    let a := (B y).inverse (fderiv ℝ (f ∘ e.symm) y)
    fderiv ℝ (fderiv ℝ (f ∘ e.symm)) y v v =
      D.hessian f (e.symm y)
          (mfderiv (𝓡 n) (𝓡 n) e.symm y v) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) +
        fderiv ℝ B y v v a - fderiv ℝ B y a v v / 2 := by
  let e := extChartAt (𝓡 n) q₀
  let B := pullbackMetricForm g e.symm
  let a := (B y).inverse (fderiv ℝ (f ∘ e.symm) y)
  have hq : e.symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source := by
    simpa only [e, extChartAt_source] using e.map_target hy
  have hh := fixedChart_hessian_formula g D q₀ hq hf v
  have hk := fixedChart_diagonal_koszul g D q₀ v a hq
  have hfield (w : EuclideanSpace ℝ (Fin n)) :
      FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (E := TangentSpace (𝓡 n)) (x := q₀) w (e.symm y) =
        mfderiv (𝓡 n) (𝓡 n) e.symm y w := by
    rw [preferredField_eq_inverseChartDerivative q₀ w hq, e.right_inv hy]
  dsimp only at hh hk
  rw [e.right_inv hy, hfield v] at hh
  rw [← chartMetricForm_fderiv_apply g q₀ hy v v a,
    ← chartMetricForm_fderiv_apply g q₀ hy a v v, hfield a,
    g.symm, chartMetricDual_pairing g q₀ hy (hf.mdifferentiableAt two_ne_zero),
    hfield v] at hk
  dsimp only
  change fderiv ℝ (fderiv ℝ (f ∘ e.symm)) y v v =
    D.hessian f (e.symm y)
        (mfderiv (𝓡 n) (𝓡 n) e.symm y v) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) +
      fderiv ℝ B y v v a - fderiv ℝ B y a v v / 2
  linarith

end PoincareConjecture.M10
