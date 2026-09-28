import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizingGeodesicLocal










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem exists_geodesic_germ_of_intrinsic_metric_segment
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {η : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hη : ContinuousOn η (Icc 0 L)) (hηU : MapsTo η (Icc 0 L) (U : Set M))
    (hsegment : ∀ s ∈ Icc 0 L, ∀ r ∈ Icc 0 L,
      intrinsicEDist g (U : Set M) (η s) (η r) = ENNReal.ofReal |s - r|)
    {t : ℝ} (ht : t ∈ Icc 0 L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ ξ : ℝ → M,
      g.IsGeodesicOn ξ {t} ∧ EqOn ξ η (Icc 0 L ∩ Ioo (t - ρ) (t + ρ)) ∧
      g.tangentNorm (ξ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ξ t 1) = 1 := by
  obtain ⟨W, hW, htW, _, hdistance⟩ :=
    exists_open_intrinsic_distance_eq g U.isOpen (hηU ht)
  have hpre : η ⁻¹' W ∈ 𝓝[Icc 0 L] t :=
    (hη t ht).preimage_mem_nhdsWithin (hW.mem_nhds htW)
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨l, r, hlr, hlrV⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
  let δ := min (t - l) (r - t) / 2
  have hδ : 0 < δ := div_pos (lt_min (by linarith [hlr.1])
    (by linarith [hlr.2])) (by norm_num)
  have hδl : δ ≤ (t - l) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδr : δ ≤ (r - t) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let a := max 0 (t - δ)
  let b := min L (t + δ)
  have hab : a < b := by
    apply max_lt_iff.mpr
    exact ⟨lt_min hL (by linarith [ht.1]),
      lt_min (by linarith [ht.2]) (by linarith)⟩
  have hsub : Icc a b ⊆ Icc 0 L :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsmall (s : ℝ) (hs : s ∈ Icc a b) : η s ∈ W := by
    apply hVsub
    refine ⟨hlrV ?_, hsub hs⟩
    have hlo : t - δ ≤ s := (le_max_right _ _).trans hs.1
    have hhi : s ≤ t + δ := hs.2.trans (min_le_right _ _)
    constructor <;> linarith [hlr.1, hlr.2]
  have htlocal : t ∈ Icc a b :=
    ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩
  obtain ⟨ρ, hρ, ξ, hξ, heq, hspeed⟩ := exists_geodesic_germ_of_metric_segment g hab
    (fun s hs r hr => (hdistance _ (hsmall s hs) _ (hsmall r hr)).symm.trans
      (hsegment s (hsub hs) r (hsub hr))) htlocal
  refine ⟨min ρ δ / 2, div_pos (lt_min hρ hδ) (by norm_num), ξ, hξ, ?_, hspeed⟩
  intro s hs
  have hmρ : min ρ δ ≤ ρ := min_le_left _ _
  have hmδ : min ρ δ ≤ δ := min_le_right _ _
  have hm : 0 < min ρ δ := lt_min hρ hδ
  apply heq
  refine ⟨⟨max_le hs.1.1 ?_, le_min hs.1.2 ?_⟩, ?_⟩
  · linarith [hs.2.1]
  · linarith [hs.2.2]
  · constructor <;> linarith [hs.2.1, hs.2.2]

omit [T2Space M] in
private theorem geodesic_germ_congr
    {g : RiemannianMetric 3 M} {ξ ζ : ℝ → M} {t : ℝ}
    (hξ : g.IsGeodesicOn ξ {t}) (heq : ζ =ᶠ[𝓝 t] ξ) :
    g.IsGeodesicOn ζ {t} := by
  intro s hs
  have hs' : s = t := mem_singleton_iff.mp hs
  subst s
  obtain ⟨p, q, w, hlocal⟩ := hξ t (by simp)
  refine ⟨p, q, w, ?_⟩
  filter_upwards [heq, hlocal] with u hu hlocalu
  exact ⟨hu.trans hlocalu.1, hlocalu.2⟩




theorem exists_geodesic_eq_intrinsic_metric_segment
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {η : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hη : ContinuousOn η (Icc 0 L)) (hηU : MapsTo η (Icc 0 L) (U : Set M))
    (hsegment : ∀ s ∈ Icc 0 L, ∀ r ∈ Icc 0 L,
      intrinsicEDist g (U : Set M) (η s) (η r) = ENNReal.ofReal |s - r|) :
    ∃ ζ : ℝ → M, g.IsGeodesicOn ζ (Icc 0 L) ∧ EqOn ζ η (Icc 0 L) ∧
      ∀ t ∈ Icc 0 L,
        g.tangentNorm (ζ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ζ t 1) = 1 := by
  obtain ⟨ρ₀, hρ₀, ξ₀, hξ₀, heq₀, hspeed₀⟩ :=
    exists_geodesic_germ_of_intrinsic_metric_segment g U hL hη hηU hsegment
      (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)
  obtain ⟨ρ₁, hρ₁, ξ₁, hξ₁, heq₁, hspeed₁⟩ :=
    exists_geodesic_germ_of_intrinsic_metric_segment g U hL hη hηU hsegment
      (show L ∈ Icc 0 L from ⟨hL.le, le_rfl⟩)
  let ζ := fun t => if t < 0 then ξ₀ t else if L < t then ξ₁ t else η t
  have hζeq : EqOn ζ η (Icc 0 L) := by
    intro t ht
    simp only [ζ, if_neg (not_lt.mpr ht.1), if_neg (not_lt.mpr ht.2)]
  have hzero : ζ =ᶠ[𝓝 0] ξ₀ := by
    filter_upwards [Ioo_mem_nhds (show -(min ρ₀ L) < (0 : ℝ) by
      linarith [lt_min hρ₀ hL]) (show (0 : ℝ) < min ρ₀ L from lt_min hρ₀ hL)]
      with t ht
    by_cases ht0 : t < 0
    · simp only [ζ, if_pos ht0]
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      have htL : t ≤ L := (ht.2.trans_le (min_le_right _ _)).le
      rw [hζeq ⟨ht0', htL⟩]
      apply (heq₀ ?_).symm
      refine ⟨⟨ht0', htL⟩, ?_⟩
      constructor
      · simp only [zero_sub]
        linarith
      · simpa only [zero_add] using ht.2.trans_le (min_le_left _ _)
  have hone : ζ =ᶠ[𝓝 L] ξ₁ := by
    filter_upwards [Ioo_mem_nhds (show L - min ρ₁ L < L by
      linarith [lt_min hρ₁ hL]) (show L < L + min ρ₁ L by
      linarith [lt_min hρ₁ hL])] with t ht
    have ht0 : 0 ≤ t := by have := min_le_right ρ₁ L; linarith [ht.1]
    by_cases hLt : L < t
    · simp only [ζ, if_neg (not_lt.mpr ht0), if_pos hLt]
    · have htL : t ≤ L := le_of_not_gt hLt
      rw [hζeq ⟨ht0, htL⟩]
      apply (heq₁ ?_).symm
      refine ⟨⟨ht0, htL⟩, ?_⟩
      have := min_le_left ρ₁ L
      constructor <;> linarith [ht.1, ht.2]
  have hgerms (t : ℝ) (ht : t ∈ Icc 0 L) :
      ∃ ξ : ℝ → M, g.IsGeodesicOn ξ {t} ∧ ζ =ᶠ[𝓝 t] ξ ∧
        g.tangentNorm (ξ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ξ t 1) = 1 := by
    rcases eq_or_lt_of_le ht.1 with h | ht0
    · subst t
      exact ⟨ξ₀, hξ₀, hzero, hspeed₀⟩
    rcases eq_or_lt_of_le ht.2 with h | htL
    · subst t
      exact ⟨ξ₁, hξ₁, hone, hspeed₁⟩
    obtain ⟨ρ, hρ, ξ, hξ, heq, hspeed⟩ :=
      exists_geodesic_germ_of_intrinsic_metric_segment g U hL hη hηU hsegment ht
    refine ⟨ξ, hξ, ?_, hspeed⟩
    filter_upwards [Ioo_mem_nhds ht0 htL,
      Ioo_mem_nhds (show t - ρ < t by linarith) (show t < t + ρ by linarith)]
      with s hs hnear
    exact (hζeq ⟨hs.1.le, hs.2.le⟩).trans (heq ⟨⟨hs.1.le, hs.2.le⟩, hnear⟩).symm
  refine ⟨ζ, ?_, hζeq, ?_⟩
  · intro t ht
    obtain ⟨ξ, hξ, heq, _⟩ := hgerms t ht
    exact geodesic_germ_congr hξ heq t (by simp)
  · intro t ht
    obtain ⟨ξ, _, heq, hspeed⟩ := hgerms t ht
    rw [heq.mfderiv_eq, heq.self_of_nhds]
    exact hspeed




theorem exists_intrinsic_unit_geodesic_minimizer
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1))
    (hγU : MapsTo γ (Icc (0 : ℝ) 1) (U : Set M))
    (hmin : g.pathELength γ 0 1 = intrinsicEDist g (U : Set M) (γ 0) (γ 1))
    (hfinite : g.pathELength γ 0 1 ≠ ⊤) (hne : γ 0 ≠ γ 1) :
    let L := (g.pathELength γ 0 1).toReal
    ∃ ζ : ℝ → M, ∃ c : ℝ → ℝ,
      0 < L ∧ ζ 0 = γ 0 ∧ ζ L = γ 1 ∧ g.IsGeodesicOn ζ (Icc 0 L) ∧
      MapsTo ζ (Icc 0 L) (U : Set M) ∧
      ζ '' Icc 0 L = γ '' Icc (0 : ℝ) 1 ∧
      ContinuousOn c (Icc (0 : ℝ) 1) ∧ MonotoneOn c (Icc (0 : ℝ) 1) ∧
      c 0 = 0 ∧ c 1 = L ∧ c '' Icc (0 : ℝ) 1 = Icc 0 L ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ζ (c t) = γ t) ∧
      (∀ t ∈ Icc 0 L,
        g.tangentNorm (ζ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) ζ t 1) = 1) ∧
      ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
        intrinsicEDist g (U : Set M) (ζ s) (ζ t) = ENNReal.ofReal |s - t| := by
  obtain ⟨η, c, hη0, hη1, hηcont, hηU, hηimage, _, hccont, hcmono,
    hc0, hc1, hcimage, hread, hdist⟩ :=
    exists_intrinsic_arcLength_minimizer g U hγ hγU hmin hfinite
  have hL : 0 < (g.pathELength γ 0 1).toReal := by
    apply lt_of_le_of_ne ENNReal.toReal_nonneg
    intro heq
    rw [← heq] at hη1
    exact hne (hη0.symm.trans hη1)
  obtain ⟨ζ, hζ, heq, hspeed⟩ :=
    exists_geodesic_eq_intrinsic_metric_segment g U hL hηcont hηU hdist
  refine ⟨ζ, c, hL, (heq ⟨le_rfl, hL.le⟩).trans hη0,
    (heq ⟨hL.le, le_rfl⟩).trans hη1, hζ, ?_, ?_, hccont, hcmono,
    hc0, hc1, hcimage, ?_, hspeed, ?_⟩
  · intro t ht
    rw [heq ht]
    exact hηU ht
  · exact (image_congr (fun t ht => heq ht)).trans hηimage
  · intro t ht
    have hct : c t ∈ Icc 0 (g.pathELength γ 0 1).toReal := by
      rw [← hcimage]
      exact mem_image_of_mem c ht
    exact (heq hct).trans (hread t ht)
  · intro s hs t ht
    rw [heq hs, heq ht]
    exact hdist s hs t ht

end PoincareConjecture.M28
