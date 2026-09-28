import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.MetricFrameReflection






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)





theorem halfDisk_metricFrame_reality_of_label
    {g : RiemannianMetric n E} {H : ℂ → E} {r t : ℝ}
    {c : ℝ → E} {sigma : ℝ → ℝ}
    (hc : DifferentiableAt ℝ c (sigma t)) (hsigma : ContDiff ℝ 1 sigma)
    {V : E → E} (j : Fin n)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hboundary : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → H (s : ℂ) = c (sigma s))
    (ht : ‖(t : ℂ)‖ < r)
    (hV : V (H (t : ℂ)) = deriv c (sigma t))
    (hj : V (H (t : ℂ)) j ≠ 0)
    (hdiag :
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (t : ℂ)
      g.inner (H (t : ℂ)) (T 1) (T 1) = g.inner (H (t : ℂ)) (T I) (T I))
    (hmixed :
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (t : ℂ)
      g.inner (H (t : ℂ)) (T 1) (T I) = 0) :
    metricBoundaryReflection j
        (halfDiskFramedGradient H
          (fun q => complexifyOperator (metricRowFrame (g.inner q) (V q) j)) r (t : ℂ)) =
      halfDiskFramedGradient H
        (fun q => complexifyOperator (metricRowFrame (g.inner q) (V q) j)) r (t : ℂ) := by
  have hd := halfDisk_hasDerivAt_diameter hH ht
  have hchain := hc.hasDerivAt.scomp t
    ((hsigma.differentiable one_ne_zero) t).hasDerivAt
  have heq : (fun s : ℝ => H (s : ℂ)) =ᶠ[𝓝 t] c ∘ sigma := by
    filter_upwards [continuous_ofReal.norm.continuousAt.eventually (gt_mem_nhds ht)] with s hs
    exact hboundary s hs.le
  have hder := hd.unique (hchain.congr_of_eventuallyEq heq)
  have hcol : ∃ a : ℝ,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) (t : ℂ) 1 =
        a • V (H (t : ℂ)) := by
    refine ⟨deriv sigma t, ?_⟩
    rw [hV]
    exact hder
  exact metricRowFrame_boundary_reflection (g.inner (H (t : ℂ))) (V (H (t : ℂ)))
    _ _ j hj (g.pos (H (t : ℂ))) hcol hdiag hmixed

end PoincareConjecture.M64
