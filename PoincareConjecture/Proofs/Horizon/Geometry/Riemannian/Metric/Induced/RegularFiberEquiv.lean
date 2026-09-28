import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Equivalence


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology
namespace PoincareConjecture.RiemannianMetric
variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
  [IsManifold (𝓡 (m+k)) ∞ M]
  {f h : M → Fin k → ℝ} {U V : Opens M} {c d : Fin k → ℝ}
  (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
  (hh : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ h)
  (hregf : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
  (hregh : ∀ x ∈ V, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) h x))
  (he : ∀ x, (x ∈ U ∧ f x = c) ↔ (x ∈ V ∧ h x = d))
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
  ⟨finrank_euclideanSpace_fin⟩


theorem openRegularFiberMetric_inner_equivOfEq
    (g : RiemannianMetric (m+k) M) (x : openFiber f U c)
    (v w : EuclideanSpace ℝ (Fin m)) :
    letI := openFiberChartedSpace (m := m) hf U hregf c
    letI := openFiberChartedSpace (m := m) hh V hregh d
    letI := isManifold_openFiber (m := m) hf U hregf c
    letI := isManifold_openFiber (m := m) hh V hregh d
    (openRegularFiberMetric hf U hregf c g).inner x v w =
      (openRegularFiberMetric hh V hregh d g).inner (openFiberEquivOfEq he x)
        (mfderiv (𝓡 m) (𝓡 m) (openFiberEquivOfEq he) x v)
        (mfderiv (𝓡 m) (𝓡 m) (openFiberEquivOfEq he) x w) := by
  let := openFiberChartedSpace (m := m) hf U hregf c
  let := openFiberChartedSpace (m := m) hh V hregh d
  let := isManifold_openFiber (m := m) hf U hregf c
  let := isManifold_openFiber (m := m) hh V hregh d
  let e := openFiberDiffeomorphOfEq (m := m) hf hh hregf hregh he
  have hcomp := mfderiv_comp x
    ((contMDiff_openFiberIncl hh V hregh d (e x)).mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiable (by simp) x)
  have heq : openFiberIncl h V d ∘ e = openFiberIncl f U c := rfl
  rw [heq] at hcomp
  change (openRegularFiberMetric hf U hregf c g).inner x v w =
    (openRegularFiberMetric hh V hregh d g).inner (e x)
      (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w)
  simp only [openRegularFiberMetric_inner]
  rw [hcomp]
  rfl


theorem openRegularFiberMetric_edist_equivOfEq
    (g : RiemannianMetric (m+k) M) (x y : openFiber f U c) :
    letI := openFiberChartedSpace (m := m) hf U hregf c
    letI := openFiberChartedSpace (m := m) hh V hregh d
    letI := isManifold_openFiber (m := m) hf U hregf c
    letI := isManifold_openFiber (m := m) hh V hregh d
    (openRegularFiberMetric hh V hregh d g).edist
        (openFiberEquivOfEq he x) (openFiberEquivOfEq he y) =
      (openRegularFiberMetric hf U hregf c g).edist x y := by
  let := openFiberChartedSpace (m := m) hf U hregf c
  let := openFiberChartedSpace (m := m) hh V hregh d
  let := isManifold_openFiber (m := m) hf U hregf c
  let := isManifold_openFiber (m := m) hh V hregh d
  exact edist_eq_of_diffeomorph_metric_pullback
    (openRegularFiberMetric hf U hregf c g) (openRegularFiberMetric hh V hregh d g)
    (openFiberDiffeomorphOfEq (m := m) hf hh hregf hregh he)
    (openRegularFiberMetric_inner_equivOfEq hf hh hregf hregh he g) x y
end PoincareConjecture.RiemannianMetric
