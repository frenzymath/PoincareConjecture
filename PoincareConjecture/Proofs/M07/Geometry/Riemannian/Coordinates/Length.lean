import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem tangentNorm_chart_curve
    (g : RiemannianMetric n M) (p : M)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} {v : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hq : HasDerivAt q v t) (ht : q t ∈ (extChartAt (𝓡 n) p).target) :
    g.tangentNorm ((extChartAt (𝓡 n) p).symm (q t))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun s => (extChartAt (𝓡 n) p).symm (q s)) t 1) =
      Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (q t) v v) := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds ht)).mdifferentiableAt (by simp)
  have hqm : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) q t :=
    mdifferentiableAt_iff_differentiableAt.mpr hq.differentiableAt
  have hchain := mfderiv_comp t hc hqm
  have hvel : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
      (fun s => (extChartAt (𝓡 n) p).symm (q s)) t 1 =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm (q t) v := by
    have h := congrArg (fun L => L 1) hchain
    change _ = mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p).symm (q t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) q t 1) at h
    have hq1 : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) q t 1 = v := by
      rw [mfderiv_eq_fderiv]
      exact hq.deriv
    rw [hq1] at h
    convert! h using 1
  rw [hvel]
  rfl


theorem pathELength_chart_curve_of_energy
    (g : RiemannianMetric n M) (p : M)
    {q w : ℝ → EuclideanSpace ℝ (Fin n)} {a b R : ℝ}
    (hU : ∀ t ∈ Icc a b, q t ∈ (extChartAt (𝓡 n) p).target)
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (w t) t)
    (henergy : ∀ t ∈ Icc a b,
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (q t) (w t) (w t) = R) :
    g.pathELength (fun t => (extChartAt (𝓡 n) p).symm (q t)) a b =
      ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (b - a) := by
  rw [pathELength_eq_lintegral_tangentNorm]
  have hfn : (fun t => ENNReal.ofReal
      (g.tangentNorm ((extChartAt (𝓡 n) p).symm (q t))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun s => (extChartAt (𝓡 n) p).symm (q s)) t 1))) =ᵐ[
      volume.restrict (Icc a b)] fun _ => ENNReal.ofReal (Real.sqrt R) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [g.tangentNorm_chart_curve p (hq t ht) (hU t ht), henergy t ht]
  rw [lintegral_congr_ae hfn, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]



theorem edist_chart_curve_le_of_energy
    (g : RiemannianMetric n M) (p : M)
    {q w : ℝ → EuclideanSpace ℝ (Fin n)} {a b R : ℝ} (hab : a ≤ b)
    (hU : ∀ t ∈ Icc a b, q t ∈ (extChartAt (𝓡 n) p).target)
    (hC : ContDiffOn ℝ 1 q (Icc a b))
    (hq : ∀ t ∈ Icc a b, HasDerivAt q (w t) t)
    (henergy : ∀ t ∈ Icc a b,
      g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (q t) (w t) (w t) = R) :
    g.edist ((extChartAt (𝓡 n) p).symm (q a)) ((extChartAt (𝓡 n) p).symm (q b)) ≤
      ENNReal.ofReal (Real.sqrt R) * ENNReal.ofReal (b - a) := by
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1
      (fun t => (extChartAt (𝓡 n) p).symm (q t)) (Icc a b) := by
    exact (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := 1) p).comp
      (contMDiffOn_iff_contDiffOn.mpr hC) hU
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab).trans_eq
    (g.pathELength_chart_curve_of_energy p hU hq henergy)

end PoincareConjecture.RiemannianMetric
