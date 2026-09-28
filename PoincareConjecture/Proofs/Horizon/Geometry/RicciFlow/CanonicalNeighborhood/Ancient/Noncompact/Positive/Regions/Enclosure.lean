import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Separation.Surrounding

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NoncompactKappa.Positive

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [ConnectedSpace M]
  {g : RiemannianMetric 3 M}

theorem neck_sphere_radial_bounds (N : EpsilonNeck g) (p : M)
    {x : M} (hx : x ∈ N.central_sphere) :
    (g.edist p N.center).toReal - (2 * Real.pi) * N.scale ≤ (g.edist p x).toReal ∧
      (g.edist p x).toReal ≤ (g.edist p N.center).toReal + (2 * Real.pi) * N.scale := by
  have hdiam := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (N.edist_central_sphere_le_two_pi_mul_scale N.center_on_central_sphere hx)
  rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) N.scale_pos.le)] at hdiam
  have h := abs_le.mp ((g.abs_toReal_edist_sub_le p N.center x).trans hdiam)
  constructor <;> linarith

theorem radial_ball_subset_side
    [NoncompactSpace M] (S : RiemannianMetric.PointSoulData g)
    (N : EpsilonNeck g) {A B : Set M}
    (hA : IsOpen A) (hB : IsOpen B) (hdisjoint : Disjoint A B)
    (hcover : A ∪ B = N.central_sphereᶜ) (hcenter : S.center ∈ A)
    {r : ℝ} (hr : 0 < r)
    (hinner : r ≤ (g.edist S.center N.center).toReal - (2 * Real.pi) * N.scale) :
    {x | (g.edist S.center x).toReal < r} ⊆ A := by
  have hsubset : {x | (g.edist S.center x).toReal < r} ⊆ A ∪ B := by
    intro x hx
    rw [hcover]
    intro hxsphere
    exact (not_lt_of_ge (hinner.trans (neck_sphere_radial_bounds N S.center hxsphere).1)) hx
  rcases (S.radial.isConnected_distance_interior hr).isPreconnected.subset_or_subset
      hA hB hdisjoint hsubset with hleft | hright
  · exact hleft
  · have hp : S.center ∈ {x | (g.edist S.center x).toReal < r} := by
      simpa only [mem_ofPred_eq, RiemannianMetric.edist,
        Manifold.riemannianEDist_self, ENNReal.toReal_zero] using hr
    exact (Set.disjoint_left.mp hdisjoint hcenter (hright hp)).elim

theorem compact_side_radial_bound
    [NoncompactSpace M] (S : RiemannianMetric.PointSoulData g)
    (N : EpsilonNeck g) {A : Set M}
    (hcompact : IsCompact (closure A)) (hfrontier : frontier A = N.central_sphere)
    (hcenter : S.center ∈ A) :
    closure A ⊆ {x | (g.edist S.center x).toReal ≤
      (g.edist S.center N.center).toReal + (2 * Real.pi) * N.scale} := by
  obtain ⟨y, hy, hmax⟩ := hcompact.exists_isMaxOn ⟨S.center, subset_closure hcenter⟩
    (g.continuous_toReal_edist S.center).continuousOn
  have hbound : (g.edist S.center y).toReal ≤
      (g.edist S.center N.center).toReal + (2 * Real.pi) * N.scale := by
    by_cases hyp : y = S.center
    · subst y
      simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self,
        ENNReal.toReal_zero]
      exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (by positivity) N.scale_pos.le)
    · have hyfrontier : y ∈ frontier A := by
        refine ⟨hy, ?_⟩
        intro hyinterior
        apply S.radial.not_isLocalMax_distance hyp
        exact hmax.isLocalMax (Filter.mem_of_superset
          (isOpen_interior.mem_nhds hyinterior) (interior_subset.trans subset_closure))
      exact (neck_sphere_radial_bounds N S.center (hfrontier ▸ hyfrontier)).2
  exact fun x hx => (hmax hx).trans hbound

theorem exists_quantitative_neck_regions
    [NoncompactSpace M] (S : RiemannianMetric.PointSoulData g)
    (hc : MetricComplete g) (N : EpsilonNeck g)
    (hN : N.epsilon ≤ neckSeparationThreshold) :
    ∃ A B : Set M,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = N.central_sphereᶜ ∧
      frontier A = N.central_sphere ∧ frontier B = N.central_sphere ∧
      IsCompact (closure A) ∧ S.center ∈ A ∧
      (∀ r : ℝ, 0 < r →
        r ≤ (g.edist S.center N.center).toReal - (2 * Real.pi) * N.scale →
        {x | (g.edist S.center x).toReal < r} ⊆ A) ∧
      closure A ⊆ {x | (g.edist S.center x).toReal ≤
        (g.edist S.center N.center).toReal + (2 * Real.pi) * N.scale} ∧
      ((N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
        (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A)) := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hdisjoint, hcover, hfA, hfB, hcompact,
    hcenter, _, hsides⟩ := S.exists_surrounding_neck_regions hc N hN
  exact ⟨A, B, hA, hB, hAc, hBc, hdisjoint, hcover, hfA, hfB, hcompact,
    hcenter, fun _ hr hi => radial_ball_subset_side S N hA hB hdisjoint hcover hcenter hr hi,
    compact_side_radial_bound S N hcompact hfA hcenter, hsides⟩

end PoincareConjecture.NoncompactKappa.Positive
