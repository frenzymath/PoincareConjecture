import PoincareLib.Geometry.Riemannian.Soul.Separation.Neck
import PoincareLib.Geometry.Riemannian.Soul.Separation.BoundaryDistance
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Depth.Points

/-!
# Small necks surround the point soul

Radial distance has no local maximum away from the soul. A compact neck side
omitting the soul would consequently have depth at most its boundary diameter,
contradicting the deep half-neck point supplied by the metric comparison.

Reference: Morgan--Tian, Lemma 2.20, first assertion, pp. 31--32.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.RiemannianMetric.RadialHomeomorph

variable {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M} {p : M}

theorem center_mem_of_compact_neck_side
    (H : RadialHomeomorph g p) (hc : MetricComplete g)
    (N : EpsilonNeck g) (hN : N.epsilon ≤ neckSeparationThreshold)
    {A : Set M} (hA : IsOpen A) (hcompact : IsCompact (closure A))
    (hfront : frontier A = N.central_sphere)
    (hhalf : N.region (-N.epsilon⁻¹) 0 ⊆ A ∨ N.region 0 N.epsilon⁻¹ ⊆ A) :
    p ∈ A := by
  have hinv := inv_pos.mpr N.epsilon_pos
  have hdeep : ∃ x ∈ A, ∀ y ∈ N.central_sphere,
      (2 * Real.pi) * N.scale < (g.edist x y).toReal := by
    rcases hhalf with hneg | hpos
    · obtain ⟨x, hx, haxis, hdepth⟩ :=
        N.exists_deep_point_of_epsilon_le hN (-1) (by norm_num)
      have heq : (-1 : ℝ) / (2 * N.epsilon) = -N.epsilon⁻¹ / 2 := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [heq] at haxis
      exact ⟨x, hneg ⟨hx, by rw [haxis]; linarith, by rw [haxis]; linarith⟩, hdepth⟩
    · obtain ⟨x, hx, haxis, hdepth⟩ :=
        N.exists_deep_point_of_epsilon_le hN 1 (by norm_num)
      have heq : (1 : ℝ) / (2 * N.epsilon) = N.epsilon⁻¹ / 2 := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [heq] at haxis
      exact ⟨x, hpos ⟨hx, by rw [haxis]; linarith, by rw [haxis]; linarith⟩, hdepth⟩
  obtain ⟨x, hx, hdepth⟩ := hdeep
  by_contra hp
  have hdiam : ∀ y ∈ frontier A, ∀ z ∈ frontier A,
      (g.edist y z).toReal ≤ (2 * Real.pi) * N.scale := by
    intro y hy z hz
    rw [hfront] at hy hz
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (N.edist_central_sphere_le_two_pi_mul_scale hy hz)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (by positivity) N.scale_pos.le)] at h
  obtain ⟨y, hy, hxy⟩ := H.exists_frontier_distance_le_diameter hc hA hcompact hp hdiam hx
  rw [hfront] at hy
  exact (not_lt_of_ge hxy) (hdepth y hy)

end PoincareMT.RiemannianMetric.RadialHomeomorph

namespace PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}

/-- The same point-soul data orient every sufficiently small neck by its
compact complementary side. The end side remains unbounded in the supplied
Euclidean coordinates. -/
theorem PointSoulData.exists_surrounding_neck_regions
    (P : PointSoulData g) (hc : MetricComplete g)
    (N : EpsilonNeck g) (hN : N.epsilon ≤ neckSeparationThreshold) :
    ∃ A B : Set M,
      IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = N.central_sphereᶜ ∧
      frontier A = N.central_sphere ∧ frontier B = N.central_sphere ∧
      IsCompact (closure A) ∧ P.center ∈ A ∧
      ¬Bornology.IsBounded (P.euclidean.symm.toHomeomorph '' B) ∧
      ((N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
        (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A)) := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hneg, hpos,
      hside, _, _⟩ := exists_neck_regions_of_pointSoulData P N
  rcases hside with ⟨hcompact, hunbounded⟩ | ⟨hcompact, hunbounded⟩
  · exact ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hcompact,
      P.radial.center_mem_of_compact_neck_side hc N hN hA hcompact hfA (Or.inl hneg),
      hunbounded, Or.inl ⟨hneg, hpos⟩⟩
  · exact ⟨B, A, hB, hA, hBc, hAc, hdisj.symm,
      (union_comm B A).trans hcover, hfB, hfA, hcompact,
      P.radial.center_mem_of_compact_neck_side hc N hN hB hcompact hfB (Or.inr hpos),
      hunbounded, Or.inr ⟨hneg, hpos⟩⟩

end PoincareMT.RiemannianMetric

universe u

/-- A universal neck threshold gives soul-to-end separation directly from
completeness and strict positive sectional curvature. -/
theorem PoincareMT.RiemannianMetric.exists_universal_soul_neck_separation_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 2 ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [ConnectedSpace M] [Nonempty M] [NoncompactSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M],
      ∀ (g : PoincareMT.RiemannianMetric 3 M) (D : PoincareMT.LeviCivitaData g),
        PoincareMT.MetricComplete g → D.StrictlyPositiveSectionalCurvature →
      ∃ P : PoincareMT.RiemannianMetric.PointSoulData g,
      ∀ N : PoincareMT.EpsilonNeck g, N.epsilon ≤ ε₀ →
      ∃ A B : Set M,
        IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
        Disjoint A B ∧ A ∪ B = N.central_sphereᶜ ∧
        frontier A = N.central_sphere ∧ frontier B = N.central_sphere ∧
        IsCompact (closure A) ∧ P.center ∈ A ∧
        ((N.region (-N.epsilon⁻¹) 0 ⊆ A ∧ N.region 0 N.epsilon⁻¹ ⊆ B) ∨
          (N.region (-N.epsilon⁻¹) 0 ⊆ B ∧ N.region 0 N.epsilon⁻¹ ⊆ A)) := by
  refine ⟨PoincareMT.neckSeparationThreshold, PoincareMT.neckSeparationThreshold_pos,
    PoincareMT.neckSeparationThreshold_lt_half, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ g D hc hpos
  obtain ⟨P⟩ := PoincareMT.RiemannianMetric.exists_pointSoulData_of_strictlyPositiveSectionalCurvature
    g D hc hpos
  refine ⟨P, ?_⟩
  intro N hN
  obtain ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hcompact, hp,
      _, hhalf⟩ := P.exists_surrounding_neck_regions hc N hN
  exact ⟨A, B, hA, hB, hAc, hBc, hdisj, hcover, hfA, hfB, hcompact, hp, hhalf⟩
