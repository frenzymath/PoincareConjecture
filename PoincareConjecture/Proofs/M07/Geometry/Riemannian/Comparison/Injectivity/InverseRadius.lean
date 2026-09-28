import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Collision
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.ReturnDirection
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem hasFDerivAt_half_squared_inverse_radius
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {q : M} (hq : q ∈ e.target)
    (hgauss : ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner q (mfderiv (𝓡 n) (𝓡 n) e (e.symm q) (e.symm q))
        (mfderiv (𝓡 n) (𝓡 n) e (e.symm q) w) = inner ℝ (e.symm q) w) :
    HasFDerivAt
      (fun y => ‖e.symm ((extChartAt (𝓡 n) q).symm y)‖ ^ 2 / 2)
      (show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from
        g.inner q (mfderiv (𝓡 n) (𝓡 n) e (e.symm q) (e.symm q)))
      (extChartAt (𝓡 n) q q) := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) q
  have hcq : c.symm (c q) = q := c.left_inv (mem_extChartAt_source q)
  have hediff : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c q) :=
    ((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds (mem_extChartAt_target q))).mdifferentiableAt
        (by norm_num)
  have hd := mfderiv_comp_of_eq (hediff.mdifferentiableAt_symm hq) hc hcq
  have hcder (u : E) : mfderiv (𝓡 n) (𝓡 n) c.symm (c q) u = u := by
    have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := q)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
    exact congrArg (fun L => L u) h
  have hd' : fderiv ℝ (e.symm ∘ c.symm) (c q) = mfderiv (𝓡 n) (𝓡 n) e.symm q := by
    apply ContinuousLinearMap.ext
    intro u
    have h := congrArg (fun L => L u) hd
    change (mfderiv (𝓡 n) (𝓡 n) (e.symm ∘ c.symm) (c q)) u =
      (mfderiv (𝓡 n) (𝓡 n) e.symm (c.symm (c q)))
        ((mfderiv (𝓡 n) (𝓡 n) c.symm (c q)) u) at h
    rw [hcder] at h
    rw [mfderiv_eq_fderiv] at h
    change (fderiv ℝ (e.symm ∘ c.symm) (c q)) u =
      (mfderiv (𝓡 n) (𝓡 n) e.symm (c.symm (c q))) u at h
    exact h.trans (congrArg (fun z : M => (mfderiv (𝓡 n) (𝓡 n) e.symm z) u) hcq)
  have hi : DifferentiableAt ℝ (e.symm ∘ c.symm) (c q) :=
    mdifferentiableAt_iff_differentiableAt.mp
      ((hediff.mdifferentiableAt_symm hq).comp_of_eq (c q) hc hcq)
  have hs := hi.hasFDerivAt.norm_sq.const_smul (1 / 2 : ℝ)
  have hs' := hs.congr_of_eventuallyEq
    (show (fun y : E => ‖e.symm (c.symm y)‖ ^ 2 / 2) =ᶠ[𝓝 (c q)]
      (1 / 2 : ℝ) • (fun y : E => ‖(e.symm ∘ c.symm) y‖ ^ 2) from
      Eventually.of_forall (fun y => by
        change ‖e.symm (c.symm y)‖ ^ 2 / 2 = (1 / 2 : ℝ) * ‖e.symm (c.symm y)‖ ^ 2
        ring))
  apply hs'.congr_fderiv
  apply ContinuousLinearMap.ext
  intro u
  have hback := congrArg (fun L => L u) (hediff.comp_symm_deriv hq)
  have hg := hgauss (mfderiv (𝓡 n) (𝓡 n) e.symm q u)
  change (mfderiv (𝓡 n) (𝓡 n) e (e.symm q))
    ((mfderiv (𝓡 n) (𝓡 n) e.symm q) u) = u at hback
  rw [hback] at hg
  simp only [smul_apply, two_smul, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, Function.comp_apply, hcq]
  have hdu := congrArg (fun A : E →L[ℝ] E => A u) hd'
  rw [hdu]
  ring_nf
  exact hg.symm



theorem radial_velocities_eq_neg_of_minimal_collision
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {r : ℝ}
    {v w : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) (heq : f v = f w) (hne : v ≠ w)
    (ev ew : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hvs : v ∈ ev.source) (hws : w ∈ ew.source)
    (hev : EqOn f ev ev.source) (hew : EqOn f ew ew.source)
    (hvsmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ev ev.source)
    (hwsmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ew ew.source)
    (hvismooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ev.symm ev.target)
    (hwismooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ew.symm ew.target)
    (hvgauss : ∀ a : EuclideanSpace ℝ (Fin n),
      g.inner (f v) (mfderiv (𝓡 n) (𝓡 n) ev v v)
        (mfderiv (𝓡 n) (𝓡 n) ev v a) = inner ℝ v a)
    (hwgauss : ∀ a : EuclideanSpace ℝ (Fin n),
      g.inner (f v) (mfderiv (𝓡 n) (𝓡 n) ew w w)
        (mfderiv (𝓡 n) (𝓡 n) ew w a) = inner ℝ w a)
    (hmin : ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
      f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) :
    mfderiv (𝓡 n) (𝓡 n) ev v v = -mfderiv (𝓡 n) (𝓡 n) ew w w := by
  let E := EuclideanSpace ℝ (Fin n)
  have hfv : ContinuousAt f v := (ev.continuousAt hvs).congr
    (hev.eventuallyEq_of_mem (ev.open_source.mem_nhds hvs)).symm
  have hfw : ContinuousAt f w := (ew.continuousAt hws).congr
    (hew.eventuallyEq_of_mem (ew.open_source.mem_nhds hws)).symm
  have hnorm := norm_eq_of_minimal_collision hv hw heq hne hfv hfw ev ew
    hvs hws hev hew hmin
  have hvt : f v ∈ ev.target := (hev hvs).symm ▸ ev.map_source hvs
  have hwt : f v ∈ ew.target := heq.symm ▸ (hew hws).symm ▸ ew.map_source hws
  have hiv : ev.symm (f v) = v := by rw [hev hvs, ev.left_inv hvs]
  have hiw : ew.symm (f v) = w := by rw [heq, hew hws, ew.left_inv hws]
  have hvd (a : E) : mfderiv (𝓡 n) (𝓡 n) ev (ev.symm (f v)) a =
      mfderiv (𝓡 n) (𝓡 n) ev v a :=
    congrArg (fun z : E => (show E from mfderiv (𝓡 n) (𝓡 n) ev z a)) hiv
  have hwd (a : E) : mfderiv (𝓡 n) (𝓡 n) ew (ew.symm (f v)) a =
      mfderiv (𝓡 n) (𝓡 n) ew w a :=
    congrArg (fun z : E => (show E from mfderiv (𝓡 n) (𝓡 n) ew z a)) hiw
  have hdv := g.hasFDerivAt_half_squared_inverse_radius ev hvsmooth hvismooth hvt
    (by simpa only [hiv, hvd] using hvgauss)
  have hdw := g.hasFDerivAt_half_squared_inverse_radius ew hwsmooth hwismooth hwt
    (by simpa only [hiw, hwd] using hwgauss)
  simp only [hiv, hvd] at hdv
  simp only [hiw, hwd] at hdw
  have hlocal := isLocalMin_max_inverse_norm_of_minimal_collision hv hw heq hne
    ev ew hvs hws hev hew hmin
  let c := extChartAt (𝓡 n) (f v)
  have hcq : c.symm (c (f v)) = f v := c.left_inv (mem_extChartAt_source (f v))
  have hc : Tendsto c.symm (𝓝 (c (f v))) (𝓝 (f v)) := by
    simpa [c, Tendsto] using (map_extChartAt_symm_nhdsWithin_range (I := 𝓡 n) (f v)).le
  have hlocal' : IsLocalMin
      (fun y : E => max (‖ev.symm (c.symm y)‖ ^ 2 / 2)
        (‖ew.symm (c.symm y)‖ ^ 2 / 2)) (c (f v)) := by
    change ∀ᶠ y in 𝓝 (c (f v)), _ ≤ _
    simp only [hcq, hiv, hiw, hnorm, max_self]
    filter_upwards [hc hlocal] with y hy
    change max ‖ev.symm (f v)‖ ‖ew.symm (f v)‖ ≤
      max ‖ev.symm (c.symm y)‖ ‖ew.symm (c.symm y)‖ at hy
    simp only [hiv, hiw, hnorm, max_self] at hy
    rcases le_max_iff.mp hy with hy | hy
    · exact (div_le_div_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy) (by norm_num)).trans
        (le_max_left _ _)
    · exact (div_le_div_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy) (by norm_num)).trans
        (le_max_right _ _)
  apply eq_neg_of_min_max_bilinear
    (show E →L[ℝ] E →L[ℝ] ℝ from g.inner (f v)) (g.symm (f v)) (g.pos (f v))
    hdv hdw ?_ hlocal'
  have hequal : inner ℝ v v = inner ℝ w w := by
    simp only [real_inner_self_eq_norm_sq, hnorm]
  exact (hvgauss v).trans (hequal.trans (hwgauss w).symm)

end PoincareConjecture.RiemannianMetric
