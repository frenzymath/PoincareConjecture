import PoincareConjecture.Proofs.M10.ChartMetricDerivative
import PoincareConjecture.Proofs.M10.FixedChartKoszul
import PoincareConjecture.Proofs.M10.MetricDualDerivative









set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem fixedChart_scalar_contDiffAt {f : M → ℝ} (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f ((extChartAt (𝓡 n) q₀).symm y)) :
    ContDiffAt ℝ 2 (f ∘ (extChartAt (𝓡 n) q₀).symm) y := by
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) 2 (extChartAt (𝓡 n) q₀).symm y :=
    (contMDiffOn_extChartAt_symm q₀).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)
  exact (hf.comp y hc).contDiffAt

set_option backward.isDefEq.respectTransparency false in

theorem chartMetricDual_pairing (g : RiemannianMetric n M) {f : M → ℝ} (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f ((extChartAt (𝓡 n) q₀).symm y))
    (w : TangentSpace (𝓡 n) ((extChartAt (𝓡 n) q₀).symm y)) :
    let e := extChartAt (𝓡 n) q₀
    let a := (pullbackMetricForm g e.symm y).inverse (fderiv ℝ (f ∘ e.symm) y)
    g.inner (e.symm y) (mfderiv (𝓡 n) (𝓡 n) e.symm y a) w =
      mvfderiv (𝓡 n) f (e.symm y) w := by
  let e := extChartAt (𝓡 n) q₀
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) e.symm y :=
    ((contMDiffOn_extChartAt_symm q₀).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)).mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)
  have hi := positive_bilinear_isInvertible (pullbackMetricForm g e.symm y)
    (fun _ hv ↦ chartMetricForm_pos g q₀ hy hv)
  obtain ⟨L, hL⟩ := inverseChart_mfderiv_isInvertible q₀ hy
  have hLv : mfderiv (𝓡 n) (𝓡 n) e.symm y (L.symm w) = w := by
    rw [← hL]
    exact L.apply_symm_apply w
  have hdv : fderiv ℝ (f ∘ e.symm) y (L.symm w) =
      mvfderiv (𝓡 n) f (e.symm y) w := by
    have hd := mfderiv_comp_apply y hf hc (L.symm w)
    rw [mfderiv_eq_fderiv, hLv] at hd
    exact hd
  have h := congrArg (fun d : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ d (L.symm w))
    (hi.self_apply_inverse (fderiv ℝ (f ∘ e.symm) y))
  change g.inner (e.symm y)
    (mfderiv (𝓡 n) (𝓡 n) e.symm y
      ((pullbackMetricForm g e.symm y).inverse (fderiv ℝ (f ∘ e.symm) y)))
    (mfderiv (𝓡 n) (𝓡 n) e.symm y (L.symm w)) = _ at h
  rw [hLv] at h
  exact h.trans hdv

set_option backward.isDefEq.respectTransparency false in

theorem chartMetricDual_hessian (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} (q₀ : M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f ((extChartAt (𝓡 n) q₀).symm y))
    (v : EuclideanSpace ℝ (Fin n)) :
    let e := extChartAt (𝓡 n) q₀
    let B := pullbackMetricForm g e.symm
    let a := fun z ↦ (B z).inverse (fderiv ℝ (f ∘ e.symm) z)
    D.hessian f (e.symm y)
        (mfderiv (𝓡 n) (𝓡 n) e.symm y v)
        (mfderiv (𝓡 n) (𝓡 n) e.symm y v) =
      B y (fderiv ℝ a y v) v + fderiv ℝ B y (a y) v v / 2 := by
  let e := extChartAt (𝓡 n) q₀
  let B := pullbackMetricForm g e.symm
  let a := fun z ↦ (B z).inverse (fderiv ℝ (f ∘ e.symm) z)
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n))
    (E := TangentSpace (𝓡 n)) (x := q₀) v
  have hq : e.symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source := by
    simpa only [e, extChartAt_source] using e.map_target hy
  have hB : ContDiffAt ℝ 1 B y :=
    ((chartMetricForm_contDiffOn g q₀).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)).of_le (by simp)
  have hi := positive_bilinear_isInvertible (B y)
    (fun _ hv ↦ chartMetricForm_pos g q₀ hy hv)
  have hd := metricDual_fderiv_identity hB (fixedChart_scalar_contDiffAt q₀ hy hf) hi v v
  have hs := pullbackMetricForm_fderiv_symm g (hB.differentiableAt one_ne_zero) v (a y) v
  have hh := fixedChart_hessian_formula g D q₀ hq hf v
  have hk := fixedChart_diagonal_koszul g D q₀ v (a y) hq
  have hfield (w : EuclideanSpace ℝ (Fin n)) :
      FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (E := TangentSpace (𝓡 n)) (x := q₀) w (e.symm y) =
        mfderiv (𝓡 n) (𝓡 n) e.symm y w := by
    rw [preferredField_eq_inverseChartDerivative q₀ w hq, e.right_inv hy]
  dsimp only at hk hh
  rw [e.right_inv hy] at hh
  rw [← chartMetricForm_fderiv_apply g q₀ hy v v (a y),
    ← chartMetricForm_fderiv_apply g q₀ hy (a y) v v, hfield (a y)] at hk
  rw [g.symm, chartMetricDual_pairing g q₀ hy (hf.mdifferentiableAt two_ne_zero)] at hk
  rw [hfield v] at hh
  change B y (fderiv ℝ a y v) v + fderiv ℝ B y v (a y) v = _ at hd
  change fderiv ℝ B y v (a y) v = fderiv ℝ B y v v (a y) at hs
  rw [hfield v] at hk
  dsimp only
  change D.hessian f (e.symm y)
    (mfderiv (𝓡 n) (𝓡 n) e.symm y v) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) =
      B y (fderiv ℝ a y v) v + fderiv ℝ B y (a y) v v / 2
  linarith

end PoincareConjecture.M10
