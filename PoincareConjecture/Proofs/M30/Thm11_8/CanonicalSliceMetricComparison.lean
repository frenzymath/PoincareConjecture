import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.M28.Mathlib.RelativeBilinearComparison
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.RelativeMetricReadout
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M30




theorem eventually_inverse_tangent_bound_of_finite_chart_jets
    {M : Type v} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {X : ℕ → Type u} [∀ k, TopologicalSpace (X k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X k)]
    [∀ k, IsManifold (𝓡 3) ∞ (X k)] {ι : Type w} [Finite ι]
    (g : RiemannianMetric 3 M) (h : ∀ k, RiemannianMetric 3 (X k))
    (e : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X k) ∞)
    (K : Set M) (hKsource : ∀ k, K ⊆ (e k).source)
    (q : ι → M) (L : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hL : ∀ i, IsCompact (L i))
    (htarget : ∀ i, L i ⊆ (extChartAt (𝓡 3) (q i)).target)
    (hcover : K ⊆ ⋃ i, (extChartAt (𝓡 3) (q i)).symm '' L i)
    (hjets : ∀ i, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ 0
        ((h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm)))
      (iteratedFDeriv ℝ 0 (g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
      atTop (L i)) :
    ∀ᶠ k in atTop, ∀ z ∈ e k '' K, ∀ w : TangentSpace (𝓡 3) z,
      g.tangentNorm ((e k).symm z) (mfderiv (𝓡 3) (𝓡 3) (e k).symm z w) ≤
        2 * (h k).tangentNorm z w := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hsingle (i : ι) : ∀ᶠ k in atTop, ∀ z ∈ L i, ∀ v : E,
      (1 / 4 : ℝ) * g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm z v v ≤
        (h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm) z v v ∧
      (h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm) z v v ≤
        4 * g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm z v v := by
    let c := extChartAt (𝓡 3) (q i)
    have hc (z : E) (hz : z ∈ L i) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
      (contMDiffOn_extChartAt_symm (q i)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) (q i)).mem_nhds (htarget i hz))
    have hcont : ContinuousOn (g.pullbackCoefficients c.symm) (L i) :=
      fun z hz => (g.contDiffAt_pullbackCoefficients (hc z hz)).continuousAt.continuousWithinAt
    have hpos : ∀ z ∈ L i, ∀ v : E, v ≠ 0 → 0 < g.pullbackCoefficients c.symm z v v := by
      intro z hz v hv
      have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible := by
        simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
          isInvertible_mfderivWithin_extChartAt_symm (htarget i hz)
      apply g.pos
      intro hzero
      apply hv
      apply hi.injective
      change (mfderiv (𝓡 3) (𝓡 3) c.symm z) v =
        (mfderiv (𝓡 3) (𝓡 3) c.symm z) 0
      rw [map_zero]
      exact hzero
    obtain ⟨alpha, halpha, hlower⟩ := exists_uniform_bilinear_family_lower_bound (hL i) hcont hpos
    have hcoeff : TendstoUniformlyOn
        (fun k => (h k).pullbackCoefficients (e k ∘ c.symm))
        (g.pullbackCoefficients c.symm) atTop (L i) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using!
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → E)).comp_tendstoUniformlyOn (hjets i)
    filter_upwards [(Metric.tendstoUniformlyOn_iff
      (α := E →L[ℝ] E →L[ℝ] ℝ)).mp hcoeff ((3 / 4) * alpha) (by positivity)]
      with k hk z hz v
    have hh := ContinuousLinearMap.relative_quadratic_bounds_of_norm_sub_le
      (g.pullbackCoefficients c.symm z) ((h k).pullbackCoefficients (e k ∘ c.symm) z)
      halpha (show (0 : ℝ) < 3 by norm_num) (hlower z hz)
      (by simpa only [show (3 : ℝ) / (1 + 3) = 3 / 4 by norm_num,
        dist_eq_norm, norm_sub_rev] using (hk z hz).le) v
    norm_num at hh
    exact hh
  filter_upwards [Filter.eventually_all.mpr hsingle] with k hk
  have hnorm : ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ 2 * (h k).tangentNorm (e k x)
        (mfderiv (𝓡 3) (𝓡 3) (e k) x v) := by
    intro x hx v
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp (hcover hx)
    let c := extChartAt (𝓡 3) (q i)
    have hxc : x ∈ c.source := hzx ▸ c.map_target (htarget i hz)
    have hcx : c x = z := by rw [← hzx]; exact c.right_inv (htarget i hz)
    have hdiff := ((e k).contMDiffOn_toFun.contMDiffAt
      ((e k).open_source.mem_nhds (hKsource k hx))).mdifferentiableAt (by simp)
    have hrel := RiemannianMetric.relative_inner_bounds_of_chart g (h k) hxc hdiff
      (fun w => by rw [hcx]; exact hk i z hz w) v
    have henergy : g.inner x v v ≤ 4 * (h k).inner (e k x)
        (mfderiv (𝓡 3) (𝓡 3) (e k) x v) (mfderiv (𝓡 3) (𝓡 3) (e k) x v) := by
      linarith [hrel.1]
    have hh := Real.sqrt_le_sqrt henergy
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    simpa only [RiemannianMetric.tangentNorm, show Real.sqrt (4 : ℝ) = 2 by norm_num] using hh
  exact g.inverse_tangentNorm_le_of_le (h k) (e k).toOpenPartialHomeomorph
    ⟨(e k).contMDiffOn_toFun.mdifferentiableOn (by simp),
      (e k).contMDiffOn_invFun.mdifferentiableOn (by simp)⟩ (hKsource k) hnorm

end PoincareConjecture.M30
