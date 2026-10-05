import PoincareLib.Geometry.Riemannian.Hessian.Tensor
import PoincareLib.Geometry.Riemannian.ScalarOperators.Locality
import PoincareLib.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareLib.Geometry.Manifold.PartitionOfUnity.Derivative

/-!
# Regularity and support of the retained scalar operators

Smoothness of the Hessian and of metric contraction gives smoothness of the
Laplacian. Locality of the differential controls the support of the gradient
pairing used in the compact-support Green identity.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The retained scalar Laplacian preserves smoothness. -/
theorem contMDiff_laplacian (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (D.laplacian f) := by
  have htrace := (D.hessian_isSmoothCovariantTensor hf).tensorTrace (g := g) (k := 0)
  have h := htrace.2 Set.univ isOpen_univ (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)
  unfold laplacian
  simpa [contMDiffOn_univ, RiemannianMetric.tensorTrace] using h

/-- Smoothness in particular gives continuity of the retained Laplacian. -/
theorem continuous_laplacian (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (D.laplacian f) :=
  (D.contMDiff_laplacian hf).continuous

/-- The pairing of two smooth metric gradients is smooth. -/
theorem contMDiff_inner_gradient (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient u x) (D.gradient v x)) := by
  intro x
  have h := ((g.contMDiff x).clm_bundle_apply (D.contMDiffAt_gradient (hu x))).clm_bundle_apply
    (D.contMDiffAt_gradient (hv x))
  simpa using (contMDiffAt_totalSpace.mp h).2

/-- The gradient pairing in Green's identity is continuous. -/
theorem continuous_inner_gradient (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v) :
    Continuous (fun x => g.inner x (D.gradient u x) (D.gradient v x)) :=
  (D.contMDiff_inner_gradient hu hv).continuous

/-- The gradient vanishes away from the topological support, without a smoothness assumption. -/
theorem gradient_eq_zero_of_notMem_tsupport (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hx : x ∉ tsupport f) :
    D.gradient f x = 0 := by
  have heq := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [gradient, Poincare.mvfderiv_eq_of_eventuallyEq heq]
  change (g.inner x).inverse (mvfderiv (𝓡 n) (fun _ : M => (0 : ℝ)) x) = 0
  simp only [mvfderiv_const, map_zero]

/-- The retained Laplacian vanishes off the support, including at nonsmooth germs. -/
theorem laplacian_eq_zero_of_notMem_tsupport (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hx : x ∉ tsupport f) :
    D.laplacian f x = 0 := by
  have heq := notMem_tsupport_iff_eventuallyEq.mp hx
  have hd (Y : (y : M) → TangentSpace (𝓡 n) y) :
      (fun y => mvfderiv (𝓡 n) f y (Y y)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [heq.eventually_nhds] with y hy
    rw [Poincare.mvfderiv_eq_of_eventuallyEq hy]
    simp
  simp only [laplacian, hessian, hessianOnFields,
    Poincare.mvfderiv_eq_of_eventuallyEq (hd _),
    Poincare.mvfderiv_eq_of_eventuallyEq heq]
  simp

/-- The retained Laplacian does not enlarge topological support. -/
theorem tsupport_laplacian_subset (D : LeviCivitaData g) (f : M → ℝ) :
    tsupport (D.laplacian f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxf
  exact hx (D.laplacian_eq_zero_of_notMem_tsupport hxf)

/-- Compact support of a scalar function is preserved by the retained Laplacian. -/
theorem hasCompactSupport_laplacian (D : LeviCivitaData g)
    {f : M → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (D.laplacian f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (D.tsupport_laplacian_subset f)

/-- The gradient pairing is supported in the topological support of its first argument. -/
theorem tsupport_inner_gradient_subset_left (D : LeviCivitaData g)
    (u v : M → ℝ) :
    tsupport (fun x => g.inner x (D.gradient u x) (D.gradient v x)) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hxu
  exact hx (by simp [D.gradient_eq_zero_of_notMem_tsupport hxu])

/-- A compactly supported first argument gives a compactly supported gradient pairing. -/
theorem hasCompactSupport_inner_gradient (D : LeviCivitaData g)
    {u : M → ℝ} (hu : HasCompactSupport u) (v : M → ℝ) :
    HasCompactSupport (fun x => g.inner x (D.gradient u x) (D.gradient v x)) :=
  hu.of_isClosed_subset (isClosed_tsupport _) (D.tsupport_inner_gradient_subset_left u v)

/-- The metric gradient commutes with a finite sum of differentiable scalar functions. -/
theorem gradient_finset_sum (D : LeviCivitaData g) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℝ) (x : M)
    (hf : ∀ i ∈ s, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f i) x) :
    D.gradient (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, D.gradient (f i) x := by
  have hd : mvfderiv (𝓡 n) (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, mvfderiv (𝓡 n) (f i) x := by
    ext v
    simpa only [sum_apply] using
      Poincare.mvfderiv_finset_sum s f x v hf
  simp only [gradient, hd, map_sum]

end PoincareMT.LeviCivitaData
