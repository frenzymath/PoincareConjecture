import PoincareConjecture.Proofs.M28.Sec10_3_Tube.FixedWallIntrinsicSegments
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricSpace
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricRayRegularity
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem completion_radius_le_endpoint_sum_of_metric_segment
    {Y : Type*} [MetricSpace Y] (E : UniformSpace.Completion Y)
    {p q : Y} {gamma : ℝ → Y} (h0 : gamma 0 = p) (h1 : gamma 1 = q)
    (hmetric : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (gamma s) (gamma t) = |s - t| * dist p q) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      dist (gamma t : UniformSpace.Completion Y) E ≤
        dist (p : UniformSpace.Completion Y) E +
          dist (q : UniformSpace.Completion Y) E := by
  intro t ht
  have hstart := hmetric 0 (by norm_num) t ht
  rw [h0] at hstart
  have hstart' : dist p (gamma t) = t * dist p q := by
    simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hstart
  have hend := hmetric t ht 1 (by norm_num)
  rw [h1] at hend
  have hend' : dist (gamma t) q = (1 - t) * dist p q := by
    simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using hend
  have hp := dist_triangle (gamma t : UniformSpace.Completion Y)
    (p : UniformSpace.Completion Y) E
  have hq := dist_triangle (gamma t : UniformSpace.Completion Y)
    (q : UniformSpace.Completion Y) E
  have hpq := dist_triangle_right (p : UniformSpace.Completion Y)
    (q : UniformSpace.Completion Y) E
  rw [UniformSpace.Completion.dist_eq, dist_comm (gamma t) p, hstart'] at hp
  rw [UniformSpace.Completion.dist_eq, hend'] at hq
  rw [UniformSpace.Completion.dist_eq] at hpq
  nlinarith

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}

theorem exists_selected_sphere_radius_barrier
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (i : ℤ) (f : M → ℝ) (hf : ContinuousOn f T.carrier)
    (hzero : ∀ x ∈ T.carrier, f x = 0 ↔ x ∈ (T.chain.neck i).central_sphere)
    (hNU : (T.chain.neck i).carrier ⊆ (U : Set M))
    {b : ℝ} (hb : b < 1)
    (hhigh : ∀ x ∈ T.carrier, b < (A.inverse x).2 → 0 < f x)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ E : UniformSpace.Completion U,
      E ∉ Set.range ((↑) : U → UniformSpace.Completion U) →
      (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
        ∀ x : U, c < (A.inverse x).2 → dist (x : UniformSpace.Completion U) E < eta) →
      ∃ alpha : ℝ, 0 < alpha ∧
        (∃ z : U, (z : M) ∈ (T.chain.neck i).central_sphere ∧
          dist (z : UniformSpace.Completion U) E = alpha) ∧
        (∀ z : U, (z : M) ∈ (T.chain.neck i).central_sphere →
          alpha ≤ dist (z : UniformSpace.Completion U) E) ∧
        (∀ x q : U, f x ≤ 0 → 0 < f q →
          alpha - dist (q : UniformSpace.Completion U) E ≤ dist x q) ∧
        (∀ x : U, f x ≤ 0 → alpha ≤ dist (x : UniformSpace.Completion U) E) ∧
        ∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  intro E houtside htail
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  let gU := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  have hed (x y : U) : gU.edist x y = ENNReal.ofReal (dist x y) := by
    change edist x y = _
    exact edist_dist x y
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hcontinuous : Continuous r :=
    (UniformSpace.Completion.continuous_coe U).dist continuous_const
  have hpositive (x : U) : 0 < r x :=
    dist_pos.mpr fun hx => houtside ⟨x, hx⟩
  have htriangle (x y : U) :
      |r x - r y| ≤ dist x y ∧ dist x y ≤ r x + r y := by
    constructor
    · simpa only [UniformSpace.Completion.dist_eq] using
        abs_dist_sub_le (x : UniformSpace.Completion U) (y : UniformSpace.Completion U) E
    · simpa only [UniformSpace.Completion.dist_eq] using
        dist_triangle_right (x : UniformSpace.Completion U) (y : UniformSpace.Completion U) E
  let S : Set U := (Subtype.val : U → M) ⁻¹' (T.chain.neck i).central_sphere
  let center : U := ⟨(T.chain.neck i).center,
    hNU ((T.chain.neck i).central_sphere_subset (T.chain.neck i).center_on_central_sphere)⟩
  have hSnonempty : S.Nonempty := ⟨center, (T.chain.neck i).center_on_central_sphere⟩
  have hScompact : IsCompact S :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (T.chain.neck i).isCompact_central_sphere
      (fun z hz => ⟨⟨z, hNU ((T.chain.neck i).central_sphere_subset hz)⟩, rfl⟩)
  obtain ⟨z0, hz0, hminimum⟩ := hScompact.exists_isMinOn hSnonempty hcontinuous.continuousOn
  let alpha : ℝ := r z0
  have hmin (z : U) (hz : z ∈ S) : alpha ≤ r z := hminimum hz
  have hcrossBound (x q : U) (hx : f x ≤ 0) (hq : 0 < f q) :
      alpha - r q ≤ dist x q := by
    apply le_of_not_gt
    intro hbad
    have hcost : 0 < alpha - r q := lt_of_le_of_lt dist_nonneg hbad
    have hdist : gU.edist x q < ENNReal.ofReal (alpha - r q) := by
      rw [hed]
      exact (ENNReal.ofReal_lt_ofReal_iff hcost).mpr hbad
    obtain ⟨gamma, h0, h1, hgamma, hlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hdist
    have hheight : ContinuousOn (fun t => f (gamma t)) (Icc (0 : ℝ) 1) :=
      hf.comp (continuous_subtype_val.comp_continuousOn hgamma.continuousOn)
        (fun t (_ : t ∈ Icc (0 : ℝ) 1) => hUV (gamma t).property)
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hheight
      (show 0 ∈ Icc (f (gamma 0)) (f (gamma 1)) from
        ⟨by simpa only [h0] using hx, by simpa only [h1] using hq.le⟩)
    have htS : gamma t ∈ S :=
      (hzero (gamma t) (hUV (gamma t).property)).mp hft
    have hradius := (le_abs_self (r (gamma t) - r q)).trans (htriangle (gamma t) q).1
    have hescape : ENNReal.ofReal (alpha - r q) ≤ gU.edist (gamma t) q := by
      rw [hed]
      exact ENNReal.ofReal_le_ofReal (by linarith [hmin (gamma t) htS])
    have hsuffix : gU.edist (gamma t) q ≤ gU.pathELength gamma t 1 :=
      Manifold.riemannianEDist_le_pathELength
        (hgamma.mono (Icc_subset_Icc ht.1 le_rfl)) rfl h1 ht.2
    have htotal : gU.pathELength gamma t 1 ≤ gU.pathELength gamma 0 1 :=
      Manifold.pathELength_mono ht.1 le_rfl
    exact (not_lt_of_ge (hescape.trans (hsuffix.trans htotal))) hlength
  have hbarrier (x : U) (hx : f x ≤ 0) : alpha ≤ r x := by
    apply le_of_not_gt
    intro hsmallx
    obtain ⟨c, _hchalf, hc1, hdecay⟩ := htail ((alpha - r x) / 4) (by linarith)
    let d : ℝ := max (max b c) (3 / 4 : ℝ)
    have hdpos : 0 < d := lt_max_of_lt_right (by norm_num)
    have hd1 : d < 1 := max_lt (max_lt hb hc1) (by norm_num)
    obtain ⟨q0, hq0⟩ := A.tail_nonempty true hdpos hd1
    have hqread := (A.mem_tail_iff_m28 true hdpos hd1).mp hq0
    have hqU : q0 ∈ (U : Set M) := by
      rw [hU]
      exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
        ⟨hqread.1, (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans
          ((le_max_right _ _).trans_lt hqread.2)⟩
    let q : U := ⟨q0, hqU⟩
    have hqb : b < (A.inverse q).2 :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans_lt hqread.2
    have hqc : c < (A.inverse q).2 :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hqread.2
    have hqpositive : 0 < f q := hhigh q (hUV q.property) hqb
    have hqsmall : r q < (alpha - r x) / 4 := hdecay q hqc
    have hcross := hcrossBound x q hx hqpositive
    have hupper := (htriangle x q).2
    linarith
  refine ⟨alpha, hpositive z0, ⟨z0, hz0, rfl⟩, hmin, hcrossBound, hbarrier, ?_⟩
  intro x hx
  exact lt_of_not_ge fun hfx => (not_le_of_gt hx) (hbarrier x hfx)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem exists_intrinsic_segment_below_completion_radius_barrier
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ),
      (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
      (∀ p q : U, 0 < f p → 0 < f q →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (mu s) (mu t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
      ∀ p q : U,
        dist (p : UniformSpace.Completion U) E < alpha →
        dist (q : UniformSpace.Completion U) E < alpha →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            dist (mu s) (mu t) = |s - t| * dist p q) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            dist (mu t : UniformSpace.Completion U) E ≤
              dist (p : UniformSpace.Completion U) E +
                dist (q : UniformSpace.Completion U) E := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha hbarrier hsegments p q hp hq
  obtain ⟨mu, h0, h1, hcontinuous, hlower, hmetric⟩ :=
    hsegments p q (hbarrier p hp) (hbarrier q hq)
  let gU := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  have hed (x y : U) : gU.edist x y = ENNReal.ofReal (dist x y) := by
    change edist x y = _
    exact edist_dist x y
  have hreal (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (mu s) (mu t) = |s - t| * dist p q := by
    have h := hmetric s hs t ht
    rw [hed, hed, ← ENNReal.ofReal_mul (abs_nonneg (s - t))] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg
      (mul_nonneg (abs_nonneg _) dist_nonneg)).mp h
  exact ⟨mu, h0, h1, hcontinuous, hlower, hreal,
    completion_radius_le_endpoint_sum_of_metric_segment E h0 h1 hreal⟩

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem exists_smooth_intrinsic_segment_below_completion_radius_barrier
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (f : M → ℝ)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ (E : UniformSpace.Completion U) (alpha : ℝ),
      (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
      (∀ p q : U, 0 < f p → 0 < f q →
        ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (mu s) (mu t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
      ∀ p q : U,
        dist (p : UniformSpace.Completion U) E < alpha →
        dist (q : UniformSpace.Completion U) E < alpha →
        ∃ nu : ℝ → U, nu 0 = p ∧ nu 1 = q ∧
          (intrinsicOpenMetric g U).IsGeodesicOn nu (Icc 0 1) ∧
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ nu (Icc 0 1) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, (3 / 4 : ℝ) ≤ (A.inverse (nu t)).2) ∧
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (nu s) (nu t) = ENNReal.ofReal
              (|s - t| * ((intrinsicOpenMetric g U).edist p q).toReal)) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            dist (nu t : UniformSpace.Completion U) E ≤
              dist (p : UniformSpace.Completion U) E +
                dist (q : UniformSpace.Completion U) E := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha hbarrier hsegments p q hp hq
  have hedist (x y : U) :
      (intrinsicOpenMetric g U).edist x y = ENNReal.ofReal (dist x y) := by
    rw [intrinsicOpenMetric_edist, ← intrinsicOpenMetricSpace_edist g U hfinite,
      edist_dist]
  obtain ⟨mu, h0, h1, hcontinuous, hlower, hmetric, hradius⟩ :=
    exists_intrinsic_segment_below_completion_radius_barrier
      T A U f hfinite E alpha hbarrier hsegments p q hp hq
  obtain ⟨nu, hnu, heq, hsmooth⟩ :=
    exists_geodesic_eq_intrinsic_unit_metric_segment g U hfinite
      (L := dist p q) dist_nonneg hcontinuous.continuousOn hmetric
  refine ⟨nu, (heq (by norm_num)).trans h0, (heq (by norm_num)).trans h1,
    hnu, hsmooth, ?_, ?_, ?_⟩
  · intro t ht
    rw [heq ht]
    exact hlower t
  · intro s hs t ht
    rw [heq hs, heq ht, hedist, hedist,
      ENNReal.toReal_ofReal dist_nonneg, hmetric s hs t ht]
  · intro t ht
    rw [heq ht]
    exact hradius t ht

end PoincareConjecture.M28
