import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.ManifoldSecondFundamental
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.ManifoldGauss

/-!
# The actual manifold Gauss equation using the genuine disk Hessian

The metric coordinate construction and the actual Hessian transport
eliminate the coordinate second fundamental form from the tensor identity.
Source: Morgan--Tian Lemma 19.2, printed p. 438;
M65 derivation 24, twelfth stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {h : RiemannianMetric 2 LoopPlane}

/-- The actual Gauss equation for a genuine smooth disk and its induced
source metric, with its actual frozen Hessian defect in every quadratic
term. Source: MT Lemma 19.2, p. 438; derivation 24, twelfth stage. -/
theorem m65PlaneSecondFundamentalForm_gauss
    (D : LeviCivitaData g) (Ds : LeviCivitaData h)
    {f : LoopPlane → M} {U : Set LoopPlane} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f U) {x : LoopPlane} (hx : x ∈ U)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : LoopPlane,
      h.inner y a b = g.inner (f y)
        (mfderiv (𝓡 2) (𝓡 n) f y a) (mfderiv (𝓡 2) (𝓡 n) f y b))
    (u v w z : LoopPlane) :
    Ds.curvatureTensor x u v w z =
      D.curvatureTensor (f x)
        (mfderiv (𝓡 2) (𝓡 n) f x u) (mfderiv (𝓡 2) (𝓡 n) f x v)
        (mfderiv (𝓡 2) (𝓡 n) f x w) (mfderiv (𝓡 2) (𝓡 n) f x z) +
      g.inner (f x) (m65PlaneSecondFundamentalForm D Ds f x u w)
        (m65PlaneSecondFundamentalForm D Ds f x v z) -
      g.inner (f x) (m65PlaneSecondFundamentalForm D Ds f x u z)
        (m65PlaneSecondFundamentalForm D Ds f x v w) := by
  have hf' : ∀ᶠ y in 𝓝 x, ContMDiffAt (𝓡 2) (𝓡 n) ∞ f y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hf y hy).contMDiffAt (hU.mem_nhds hy)
  obtain ⟨gE, DE, hE, hGauss⟩ :=
    M65Gauss.exists_chart_gauss_curvatureTensor D Ds hf' hmetric
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] at hE hGauss
  have hB (a b : LoopPlane) := m65PlaneSecondFundamentalForm_chart D Ds DE (f x)
    hU hf hx (mem_chart_source (EuclideanSpace ℝ (Fin n)) (f x)) hE a b
  simpa only [Function.comp_apply, ← hB] using hGauss u v w z

end PoincareMT
