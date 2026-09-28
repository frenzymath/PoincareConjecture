import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.NormalizedChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Density
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_sublevel_normal_chart (D : LeviCivitaData g) {f : M → ℝ} {p : M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hgrad : D.gradient f p = 0)
    {a : ℝ} (hhess : ∀ v w, D.hessian f p v w = a * g.inner p v w) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContDiffAt ℝ ∞ (f ∘ e) 0 ∧ fderiv ℝ (f ∘ e) 0 = 0 ∧
      (∀ v, fderiv ℝ (fderiv ℝ (f ∘ e)) 0 v v = a * ‖v‖ ^ 2) ∧
      g.pullbackVolumeDensity e 0 = 1 := by
  obtain ⟨e, he0, hep, he, hei, _, hcoeff, hΓ⟩ :=
    g.exists_normalized_exponential_chart_firstJet p
  have hec := he.contMDiffAt (e.open_source.mem_nhds he0)
  have hefs : ContDiffAt ℝ ∞ (f ∘ e) 0 :=
    contMDiffAt_iff_contDiffAt.mp ((hf (e 0)).comp 0 hec)
  have hdf : fderiv ℝ (f ∘ e) 0 = 0 := by
    ext v
    have hd := mvfderiv_comp_apply 0 ((hf (e 0)).mdifferentiableAt (by simp))
      (hec.mdifferentiableAt (by simp)) v
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (f ∘ e) 0 v = _ at hd
    rw [mfderiv_eq_fderiv] at hd
    refine hd.trans ?_
    change mvfderiv (𝓡 n) f (e 0) _ = 0
    rw [hep, ← D.inner_gradient, hgrad]
    simp
  have hess (v : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fderiv ℝ (f ∘ e)) 0 v v = a * ‖v‖ ^ 2 := by
    have h := D.hessian_in_smooth_local_parametrization e he hei he0 (hf (e 0)) v v
    rw [hdf, zero_apply, sub_zero] at h
    rw [← h, hep, hhess]
    have hc := congrArg (fun B => B v v) hcoeff
    change g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 v)
      (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ v v at hc
    rw [hep] at hc
    rw [hc, real_inner_self_eq_norm_sq]
  refine ⟨e, he0, hep, he, hei, hefs, hdf, hess, ?_⟩
  have hm : Matrix.of (fun i j : Fin n => g.inner (e 0)
      (mfderiv (𝓡 n) (𝓡 n) e 0 (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) e 0 (EuclideanSpace.basisFun (Fin n) ℝ j))) = 1 := by
    ext i j
    have hc := congrArg (fun B => B (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)) hcoeff
    change g.inner (e 0)
      (mfderiv (𝓡 n) (𝓡 n) e 0 (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) e 0 (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) at hc
    simpa only [Matrix.of_apply, (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite,
      Matrix.one_apply] using hc
  simp only [RiemannianMetric.pullbackVolumeDensity, hm, Matrix.det_one, Real.sqrt_one]

end PoincareConjecture.LeviCivitaData

namespace Poincare.Topology

theorem eventually_sublevel_subset_of_unique_min
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {f : X → ℝ} (hf : Continuous f)
    {p : X} (hmin : ∀ x, f p ≤ f x) (huniq : ∀ x, f x = f p → x = p)
    {U : Set X} (hU : U ∈ 𝓝 p) :
    ∀ᶠ t in 𝓝[>] f p, {x | f x < t} ⊆ U := by
  obtain ⟨V, hVU, hVo, hpV⟩ := mem_nhds_iff.mp hU
  by_cases hV : Vᶜ.Nonempty
  · obtain ⟨q, hq, hqmin⟩ := hVo.isClosed_compl.isCompact.exists_isMinOn hV hf.continuousOn
    have hpq : f p < f q := lt_of_le_of_ne (hmin q) (by
      intro heq
      have hqp := huniq q heq.symm
      exact hq (hqp ▸ hpV))
    filter_upwards [(gt_mem_nhds hpq).filter_mono nhdsWithin_le_nhds] with t ht
    intro x hx
    apply hVU
    by_contra hxV
    have h := hqmin hxV
    exact (not_lt_of_ge h) (hx.trans ht)
  · filter_upwards [] with t x hx
    apply hVU
    by_contra hxV
    exact hV ⟨x, hxV⟩

end Poincare.Topology
