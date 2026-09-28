import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicEndRayUniqueness
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedCylinderMetricRays

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {X : Set M}

theorem selected_segment_tendsto_shortened_ray
    (T : EpsilonTubeCertificate g X) (C : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = C.tail true (1 / 2))
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∀ E : UniformSpace.Completion U,
      (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
        ∀ x : U, c < (C.inverse x).2 →
          dist (x : UniformSpace.Completion U) E < eta) →
      ∀ {b B : ℝ} {mu : ℝ → U}, 0 < B → B < b →
      (∀ s ∈ Ico (0 : ℝ) b, ∀ t ∈ Ico (0 : ℝ) b,
        dist (mu s) (mu t) = |s - t|) →
      (∀ s ∈ Ico (0 : ℝ) b,
        dist (mu s : UniformSpace.Completion U) E = b - s) →
      ∀ {arc : ℕ → ℝ → U} {length : ℕ → ℝ} {q : ℕ → U},
        (∀ n, 0 < length n) →
        Tendsto length atTop (𝓝 B) →
        Tendsto (fun n => dist (q n : UniformSpace.Completion U) E) atTop (𝓝 0) →
        (∀ n, arc n 0 = mu (b - B)) →
        (∀ n, arc n (length n) = q n) →
        (∀ n, ∀ s ∈ Icc (0 : ℝ) (length n),
          ∀ t ∈ Icc (0 : ℝ) (length n), dist (arc n s) (arc n t) = |s - t|) →
        (∀ n, ∀ t ∈ Icc (0 : ℝ) (length n),
          (3 / 4 : ℝ) ≤ (C.inverse (arc n t)).2) →
        ∀ t ∈ Ico (0 : ℝ) B,
          Tendsto (fun n => arc n t) (hyperfilter ℕ : Filter ℕ)
            (𝓝 (mu (b - B + t))) := by
  let := intrinsicOpenMetricSpace g U hfinite
  intro E htail b B mu hB hBb hmu hmuRadius
    arc length q hlengthPos hlength hdefect hanchor hendpoint harcMetric harcLower
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  have hcontinuous : Continuous r :=
    (UniformSpace.Completion.continuous_coe U).dist continuous_const
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact C.tail_subset_m28 true (by norm_num) (by norm_num)
  have hanchorRadius : r (mu (b - B)) = B := by
    dsimp [r]
    rw [hmuRadius (b - B) ⟨by linarith, by linarith⟩]
    ring
  have htriangle (x y : U) : |r x - r y| ≤ dist x y := by
    simpa only [UniformSpace.Completion.dist_eq] using
      abs_dist_sub_le (x : UniformSpace.Completion U) (y : UniformSpace.Completion U) E
  have hradiusBounds (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (length n)) :
      B - t ≤ r (arc n t) ∧ r (arc n t) ≤ length n - t + r (q n) := by
    have hstart := harcMetric n 0 ⟨le_rfl, (hlengthPos n).le⟩ t ht
    rw [hanchor n] at hstart
    have hstart' : dist (mu (b - B)) (arc n t) = t := by
      simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hstart
    have hend := harcMetric n t ht (length n) ⟨(hlengthPos n).le, le_rfl⟩
    rw [hendpoint n] at hend
    have hend' : dist (arc n t) (q n) = length n - t := by
      simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using hend
    have hlow := (le_abs_self (r (mu (b - B)) - r (arc n t))).trans
      (htriangle (mu (b - B)) (arc n t))
    have hupp := (le_abs_self (r (arc n t) - r (q n))).trans
      (htriangle (arc n t) (q n))
    rw [hanchorRadius, hstart'] at hlow
    rw [hend'] at hupp
    constructor <;> linarith
  have hprefix : ∀ T0 : ℝ, 0 < T0 → T0 < B →
      ∃ K : Set U, IsCompact K ∧
        ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T0, arc n t ∈ K := by
    intro T0 _hT0 hT0B
    obtain ⟨d, _hdhalf, hd1, hdecay⟩ := htail ((B - T0) / 2)
      (half_pos (sub_pos.mpr hT0B))
    let upper : ℝ := max d (3 / 4 : ℝ)
    have hupper : upper < 1 := max_lt hd1 (by norm_num)
    have hKambient : IsCompact (C.compactSlab (3 / 4) upper) :=
      C.isCompact_compactSlab (by norm_num) hupper
    have hKU : C.compactSlab (3 / 4) upper ⊆ (U : Set M) := by
      intro x hx
      have hxread := (C.mem_compactSlab_iff (by norm_num) hupper).mp hx
      rw [hU]
      exact (C.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
        ⟨hxread.1, (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans_le hxread.2.1⟩
    let K : Set U := (Subtype.val : U → M) ⁻¹' C.compactSlab (3 / 4) upper
    have hK : IsCompact K :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKambient
        (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)
    refine ⟨K, hK, ?_⟩
    filter_upwards [hlength.eventually (lt_mem_nhds hT0B)] with n hn
    intro t ht
    have htime : t ∈ Icc (0 : ℝ) (length n) := ⟨ht.1, ht.2.trans hn.le⟩
    have hbound := (hradiusBounds n t htime).1
    have hheightUpper : (C.inverse (arc n t)).2 ≤ d := by
      apply le_of_not_gt
      intro hhigh
      have hsmall := hdecay (arc n t) hhigh
      change r (arc n t) < (B - T0) / 2 at hsmall
      linarith [ht.2]
    change (arc n t : M) ∈ C.compactSlab (3 / 4) upper
    exact (C.mem_compactSlab_iff (by norm_num) hupper).mpr
      ⟨hUV (arc n t).property, harcLower n t htime,
        hheightUpper.trans (le_max_left _ _)⟩
  obtain ⟨sigma, hsigma0, _hsigmaIsometry, hsigmaMetric, hsigmaLimit⟩ :=
    exists_isometric_finite_ray_of_compact_prefixes hB hlength
      (Eventually.of_forall hanchor) hprefix harcMetric
  have hsigmaRadius : ∀ t ∈ Ico (0 : ℝ) B, r (sigma t) = B - t := by
    apply finite_ray_radius_eq_of_source_bounds (r := r) hcontinuous
      hlength hdefect hsigmaLimit
    intro t ht
    exact (hlength.eventually (lt_mem_nhds ht.2)).mono fun n hn =>
      hradiusBounds n t ⟨ht.1, hn.le⟩
  have hremaining : b - (b - B) = B := by ring
  have heq : ∀ t ∈ Ico (0 : ℝ) B, sigma t = mu (b - B + t) := by
    have h := intrinsic_end_ray_eq_after_interior g U hfinite E
      (a := b) (t0 := b - B) (gamma := mu) (sigma := sigma)
      ⟨by linarith, by linarith⟩ hsigma0 hmu
      (by simpa only [hremaining] using hsigmaMetric) hmuRadius
      (by simpa only [hremaining] using hsigmaRadius)
    simpa only [hremaining] using h
  intro t ht
  simpa only [heq t ht] using hsigmaLimit t ht

end PoincareConjecture.M28
