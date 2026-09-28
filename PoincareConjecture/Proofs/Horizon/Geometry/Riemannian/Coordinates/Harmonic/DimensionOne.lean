import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Orthonormal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]

lemma pullbackCoefficients_eq_of_gauss_one (g : RiemannianMetric 1 M) (p : M)
    {e : EuclideanSpace ℝ (Fin 1) → M} {U : Set (EuclideanSpace ℝ (Fin 1))}
    (hU : IsOpen U) (hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ U)
    (he : ContMDiffOn (𝓡 1) (𝓡 1) ∞ e U)
    (hgauss : ∀ z ∈ U, ∀ w : EuclideanSpace ℝ (Fin 1),
      g.pullbackCoefficients e z z w = g.inner p z w)
    {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ U)
    (v w : EuclideanSpace ℝ (Fin 1)) :
    g.pullbackCoefficients e x v w = g.inner p v w := by
  have hnonzero (z : EuclideanSpace ℝ (Fin 1)) (hz : z ∈ U) (hne : z ≠ 0) :
      g.pullbackCoefficients e z v w = g.inner p v w := by
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1) hne v
    simp only [map_smul, smul_apply, smul_eq_mul, hgauss z hz w]
  by_cases hne : x ≠ 0
  · exact hnonzero x hx hne
  · have hxzero : x = 0 := not_ne_iff.mp hne
    subst x
    have hcoeff := (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (hU.mem_nhds hzero))).continuousAt
    have hc : ContinuousAt (fun z ↦ g.pullbackCoefficients e z v w) 0 :=
      (hcoeff.clm_apply continuousAt_const).clm_apply continuousAt_const
    have hnebot : (𝓝[≠] (0 : EuclideanSpace ℝ (Fin 1))).NeBot := by
      exact Module.punctured_nhds_neBot ℝ (EuclideanSpace ℝ (Fin 1)) 0
    exact tendsto_nhds_unique_of_eventuallyEq
      (l := 𝓝[≠] (0 : EuclideanSpace ℝ (Fin 1)))
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds (x := g.inner p v w))
      (by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hzero)] with z hzne hz
        exact hnonzero z hz hzne)

theorem exists_exponential_chart_constant_metric_one (g : RiemannianMetric 1 M) (p : M) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) M,
      (0 : EuclideanSpace ℝ (Fin 1)) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e e.source ∧
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, ∀ v w : EuclideanSpace ℝ (Fin 1),
        g.pullbackCoefficients e x v w = g.inner p v w := by
  obtain ⟨e, he0, hep, he, hei, hgauss, _⟩ := g.exists_exponential_chart_gauss p
  refine ⟨e, he0, hep, he, hei, ?_⟩
  intro x hx v w
  apply g.pullbackCoefficients_eq_of_gauss_one p e.open_source he0 he ?_ hx v w
  exact hgauss

theorem exists_arclength_chart_one (g : RiemannianMetric 1 M) (p : M) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 1)) M,
      (0 : EuclideanSpace ℝ (Fin 1)) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e e.source ∧
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, ∀ v w : EuclideanSpace ℝ (Fin 1),
        g.pullbackCoefficients e x v w = inner ℝ v w := by
  obtain ⟨f, hf0, hfp, hf, hfi, hmetric⟩ := g.exists_exponential_chart_constant_metric_one p
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  let e := L.toHomeomorph.toOpenPartialHomeomorph.trans f
  have he : ContMDiffOn (𝓡 1) (𝓡 1) ∞ e e.source := by
    change ContMDiffOn (𝓡 1) (𝓡 1) ∞ (f ∘ L) e.source
    exact hf.comp (contMDiff_iff_contDiff.mpr L.contDiff).contMDiffOn
      (fun x hx ↦ hx.2)
  refine ⟨e, ⟨Set.mem_univ _, by simpa using hf0⟩, ?_, he, ?_, ?_⟩
  · change f (L 0) = p
    simpa only [map_zero] using hfp
  · change ContMDiffOn (𝓡 1) (𝓡 1) ∞ (L.symm ∘ f.symm) e.target
    exact (contMDiff_iff_contDiff.mpr L.symm.contDiff).comp_contMDiffOn
      (hfi.mono fun x hx ↦ hx.1)
  · intro x hx v w
    have hfd : MDifferentiableAt (𝓡 1) (𝓡 1) f (L x) :=
      (hf.contMDiffAt (f.open_source.mem_nhds hx.2)).mdifferentiableAt (by simp)
    have hLd : MDifferentiableAt (𝓡 1) (𝓡 1) L x :=
      mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
    have hd := mfderiv_comp x hfd hLd
    have hLm : mfderiv (𝓡 1) (𝓡 1) L x = L.toContinuousLinearMap := by
      simpa only [mfderiv_eq_fderiv] using L.hasFDerivAt.fderiv
    rw [hLm] at hd
    have hpull : g.pullbackCoefficients e x v w =
        g.pullbackCoefficients f (L x) (L v) (L w) := by
      unfold pullbackCoefficients
      simp only [ContinuousLinearMap.bilinearComp_apply]
      change g.inner (f (L x)) (mfderiv (𝓡 1) (𝓡 1) (f ∘ L) x v)
        (mfderiv (𝓡 1) (𝓡 1) (f ∘ L) x w) = _
      rw [hd]
      rfl
    rw [hpull, hmetric (L x) hx.2]
    rw [← g.chartCoefficients_center]
    exact hL v w

end PoincareConjecture.RiemannianMetric
