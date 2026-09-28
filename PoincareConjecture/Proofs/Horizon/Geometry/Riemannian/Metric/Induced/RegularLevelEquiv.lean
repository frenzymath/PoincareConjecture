import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Equivalence







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {f h : M → ℝ} {U V : Opens M} {c d : ℝ}
  (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (hh : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
  (hregf : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (hregh : ∀ x ∈ V, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) h x ≠ 0)
  (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d))

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem regularLevelMetric_inner_equivOfEq
    (g : RiemannianMetric (n + 1) M) (x : openLevelSet f U c)
    (v w : EuclideanSpace ℝ (Fin n)) :
    letI := openLevelSetChartedSpace hf U hregf n c
    letI := openLevelSetChartedSpace hh V hregh n d
    letI := isManifold_openLevelSet hf U hregf n c
    letI := isManifold_openLevelSet hh V hregh n d
    (regularLevelMetric hf U hregf c g).inner x v w =
      (regularLevelMetric hh V hregh d g).inner (openLevelEquivOfEq he x)
        (mfderiv (𝓡 n) (𝓡 n) (openLevelEquivOfEq he) x v)
        (mfderiv (𝓡 n) (𝓡 n) (openLevelEquivOfEq he) x w) := by
  let := openLevelSetChartedSpace hf U hregf n c
  let := openLevelSetChartedSpace hh V hregh n d
  let := isManifold_openLevelSet hf U hregf n c
  let := isManifold_openLevelSet hh V hregh n d
  let e := openLevelDiffeomorphOfEq hf hh n hregf hregh he
  have hcomp := mfderiv_comp x
    ((contMDiff_openLevelIncl hh V hregh n d (e x)).mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiable (by simp) x)
  have heq : openLevelIncl h V d ∘ e = openLevelIncl f U c := rfl
  rw [heq] at hcomp
  change (regularLevelMetric hf U hregf c g).inner x v w =
    (regularLevelMetric hh V hregh d g).inner (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w)
  simp only [regularLevelMetric_inner]
  rw [hcomp]
  rfl


theorem regularLevelMetric_edist_equivOfEq
    (g : RiemannianMetric (n + 1) M) (x y : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hregf n c
    letI := openLevelSetChartedSpace hh V hregh n d
    letI := isManifold_openLevelSet hf U hregf n c
    letI := isManifold_openLevelSet hh V hregh n d
    (regularLevelMetric hh V hregh d g).edist
        (openLevelEquivOfEq he x) (openLevelEquivOfEq he y) =
      (regularLevelMetric hf U hregf c g).edist x y := by
  let := openLevelSetChartedSpace hf U hregf n c
  let := openLevelSetChartedSpace hh V hregh n d
  let := isManifold_openLevelSet hf U hregf n c
  let := isManifold_openLevelSet hh V hregh n d
  exact edist_eq_of_diffeomorph_metric_pullback
    (regularLevelMetric hf U hregf c g) (regularLevelMetric hh V hregh d g)
    (openLevelDiffeomorphOfEq hf hh n hregf hregh he)
    (regularLevelMetric_inner_equivOfEq hf hh hregf hregh he g) x y

end PoincareConjecture.RiemannianMetric
