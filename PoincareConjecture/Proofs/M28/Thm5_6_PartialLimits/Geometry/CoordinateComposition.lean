import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullbackCoefficients_comp (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f (a x))
    (ha : DifferentiableAt ℝ a x) :
    g.pullbackCoefficients (f ∘ a) x =
      (g.pullbackCoefficients f (a x)).bilinearComp (fderiv ℝ a x) (fderiv ℝ a x) := by
  ext v w
  change g.inner (f (a x))
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ a) x v)
      (mfderiv (𝓡 n) (𝓡 n) (f ∘ a) x w) =
    g.inner (f (a x))
      (mfderiv (𝓡 n) (𝓡 n) f (a x) (fderiv ℝ a x v))
      (mfderiv (𝓡 n) (𝓡 n) f (a x) (fderiv ℝ a x w))
  rw [mfderiv_comp x hf ha.mdifferentiableAt, mfderiv_eq_fderiv]
  rfl

theorem pullbackCoefficients_eq_chart_pullback (g : RiemannianMetric n M) (q : M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hx : f x ∈ (extChartAt (𝓡 n) q).source) :
    g.pullbackCoefficients f x =
      (g.pullbackCoefficients (extChartAt (𝓡 n) q).symm
        ((extChartAt (𝓡 n) q) (f x))).bilinearComp
          (fderiv ℝ ((extChartAt (𝓡 n) q) ∘ f) x)
          (fderiv ℝ ((extChartAt (𝓡 n) q) ∘ f) x) := by
  let c := extChartAt (𝓡 n) q
  let a := c ∘ f
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (f x) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  have ha : ContDiffAt ℝ ∞ a x := (hc.comp x hf).contDiffAt
  have hcinv : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (a x) :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (c.map_source hx))
  have heq : c.symm ∘ a =ᶠ[𝓝 x] f := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) q).mem_nhds hx)] with y hy
    exact c.left_inv hy
  rw [← g.pullbackCoefficients_eq_of_eventuallyEq heq]
  exact g.pullbackCoefficients_comp (hcinv.mdifferentiableAt (by simp))
    (ha.differentiableAt (by simp))

end PoincareConjecture.RiemannianMetric
