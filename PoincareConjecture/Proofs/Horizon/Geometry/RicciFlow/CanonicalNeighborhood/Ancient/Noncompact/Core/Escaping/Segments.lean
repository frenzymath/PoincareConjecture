import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Separation.Surrounding
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric.PointSoulData

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}



theorem exists_minimizing_window_through_neck
    (S : PointSoulData g) (hc : MetricComplete g)
    (N : EpsilonNeck g) (hN : N.epsilon ≤ neckSeparationThreshold)
    {r : ℝ} (hr : 0 ≤ r)
    (hfar : r + (2 * Real.pi) * N.scale < (g.edist S.center N.center).toReal) :
    ∃ γ : ℝ → M, γ 0 ∈ N.central_sphere ∧
      (g.edist (γ 0) N.center).toReal ≤ (2 * Real.pi) * N.scale ∧
      ∀ s t : ℝ, |s| ≤ r → |t| ≤ r →
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  obtain ⟨A, B, hA, hB, _, _, hdisj, hcover, hfA, _, hcompact, hp, _, _⟩ :=
    S.exists_surrounding_neck_regions hc N hN
  let C := (2 * Real.pi) * N.scale
  have hC : 0 ≤ C := mul_nonneg (by positivity) N.scale_pos.le
  have hball := g.isCompact_closedBall_of_metricComplete hc N.center (r + C + 1)
  have hex : ∃ y, y ∉ closure A ∪ {z | g.edist N.center z ≤ ENNReal.ofReal (r + C + 1)} := by
    by_contra hn
    apply (hcompact.union hball).ne_univ
    push Not at hn
    exact Set.eq_univ_of_forall hn
  obtain ⟨y, hy⟩ := hex
  have hyA : y ∉ closure A := fun h => hy (Or.inl h)
  have hyfar : r + C + 1 < (g.edist N.center y).toReal := by
    have hnot : ¬ g.edist N.center y ≤ ENNReal.ofReal (r + C + 1) :=
      fun h => hy (Or.inr h)
    by_contra hn
    exact hnot ((ENNReal.le_ofReal_iff_toReal_le (g.edist_ne_top _ _)
      (by linarith)).mpr (le_of_not_gt hn))
  have hyB : y ∈ B := by
    have hys : y ∉ N.central_sphere := by
      rw [← hfA]
      exact fun h => hyA (frontier_subset_closure h)
    have hyunion : y ∈ A ∪ B := by rwa [hcover]
    exact hyunion.resolve_left (fun h => hyA (subset_closure h))
  have hpy : S.center ≠ y := by
    rintro rfl
    exact hyA (subset_closure hp)
  have hd : 0 < (g.edist S.center y).toReal :=
    ENNReal.toReal_pos (fun h => hpy (edist_eq_zero.mp h))
      (g.edist_ne_top _ _)
  obtain ⟨σ, hσ0, hσd, hgeo, _, hdist⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc S.center y hd
  let d := (g.edist S.center y).toReal
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have hlast : d ∈ Icc 0 d := ⟨hd.le, le_rfl⟩
  have hcross : ∃ a ∈ Icc 0 d, σ a ∈ N.central_sphere := by
    by_contra hn
    push Not at hn
    have hsub : σ '' Icc 0 d ⊆ A ∪ B := by
      rintro z ⟨a, ha, rfl⟩
      rw [hcover]
      exact hn a ha
    have hconn := isPreconnected_Icc.image σ hgeo.contMDiffOn.continuousOn
    have hleft := hconn.subset_left_of_subset_union hA hB hdisj hsub
      ⟨S.center, ⟨0, h0, hσ0⟩, hp⟩
    exact Set.disjoint_left.mp hdisj (hleft ⟨d, hlast, hσd⟩) hyB
  obtain ⟨a, ha, has⟩ := hcross
  have hdiam : (g.edist (σ a) N.center).toReal ≤ C := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (N.edist_central_sphere_le_two_pi_mul_scale has N.center_on_central_sphere)
    change _ ≤ (ENNReal.ofReal C).toReal at h
    rwa [ENNReal.toReal_ofReal hC] at h
  have hleftdist : (g.edist S.center (σ a)).toReal = a := by
    have h := hdist 0 h0 a ha
    rw [hσ0, zero_sub, abs_neg, abs_of_nonneg ha.1] at h
    rw [h, ENNReal.toReal_ofReal ha.1]
  have hrightdist : (g.edist (σ a) y).toReal = d - a := by
    have h := hdist a ha d hlast
    rw [hσd, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ha.2)] at h
    rw [h, ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
  have hleft : r < a := by
    have h := g.toReal_edist_triangle S.center (σ a) N.center
    rw [hleftdist] at h
    change r + C < _ at hfar
    linarith
  have hright : r < d - a := by
    have h := g.toReal_edist_triangle N.center (σ a) y
    rw [hrightdist, show g.edist N.center (σ a) = g.edist (σ a) N.center from
      edist_comm N.center (σ a)] at h
    linarith
  refine ⟨fun t => σ (t + a), by simpa only [zero_add] using has,
    by simpa only [zero_add] using hdiam, ?_⟩
  intro s t hs ht
  have hmem {u : ℝ} (hu : |u| ≤ r) : u + a ∈ Icc 0 d := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hu
    constructor <;> linarith
  simpa only [add_sub_add_right_eq_sub] using
    hdist (s + a) (hmem hs) (t + a) (hmem ht)

end PoincareConjecture.RiemannianMetric.PointSoulData
