import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Compatibility











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47



theorem terminalGerms_metric_fibre_compatibility
    {n : ℕ} {ι : Type*} {P : ι → Type*}
    [∀ i, TopologicalSpace (P i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)]
    (O : OverlapSystem P)
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (Quotient O.setoid)]
    [IsManifold (𝓡 n) ∞ (Quotient O.setoid)]
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (O.include i))
    (i j : ι)
    (ht : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (O.transition i j) (O.transition i j).source)
    (gi : RiemannianMetric n (P i)) (gj : RiemannianMetric n (P j))
    (hmetric : ∀ x ∈ (O.transition i j).source, ∀ a b,
      gi.inner x a b = gj.inner (O.transition i j x)
        (mfderiv (𝓡 n) (𝓡 n) (O.transition i j) x a)
        (mfderiv (𝓡 n) (𝓡 n) (O.transition i j) x b))
    (x : P i) (y : P j) (hxy : O.include i x = O.include j y)
    (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y)
    (ha : mfderiv (𝓡 n) (𝓡 n) (O.include i) x a =
      mfderiv (𝓡 n) (𝓡 n) (O.include j) y c)
    (hb : mfderiv (𝓡 n) (𝓡 n) (O.include i) x b =
      mfderiv (𝓡 n) (𝓡 n) (O.include j) y d) :
    gi.inner x a b = gj.inner y c d := by
  obtain ⟨hx, hxy⟩ := (O.include_eq_iff i j x y).mp hxy
  change O.transition i j x = y at hxy
  subst y
  have hnear : O.include j ∘ O.transition i j =ᶠ[𝓝 x] O.include i := by
    filter_upwards [(O.transition i j).open_source.mem_nhds hx] with z hz
    exact ((O.include_eq_iff i j z _).mpr ⟨hz, rfl⟩).symm
  have hdt := (ht.contMDiffAt ((O.transition i j).open_source.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have hderiv : (mfderiv (𝓡 n) (𝓡 n) (O.include j) (O.transition i j x)).comp
      (mfderiv (𝓡 n) (𝓡 n) (O.transition i j) x) =
        mfderiv (𝓡 n) (𝓡 n) (O.include i) x := by
    rw [← mfderiv_comp x ((hq j).mdifferentiable (by simp) _) hdt]
    exact hnear.mfderiv_eq
  let L := (hq j).mfderivToContinuousLinearEquiv (by simp) (O.transition i j x)
  have hac : mfderiv (𝓡 n) (𝓡 n) (O.transition i j) x a = c := by
    apply L.injective
    exact (congrArg (fun A => A a) hderiv).trans ha
  have hbd : mfderiv (𝓡 n) (𝓡 n) (O.transition i j) x b = d := by
    apply L.injective
    exact (congrArg (fun A => A b) hderiv).trans hb
  simpa only [hac, hbd] using hmetric x hx a b

end PoincareConjecture.M47
