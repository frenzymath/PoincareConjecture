import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.IntrinsicSpatialSystem

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

omit [IsManifold (𝓡 n) ∞ M] in

theorem m65Exists_finite_chart_cores [T2Space M] {C : Set M} (hC : IsCompact C) :
    ∃ (m : ℕ) (p : Fin m → M) (K : Fin m → Set M),
      (∀ i, IsCompact (K i)) ∧
      (∀ i, K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) ∧
      ∀ y ∈ C, ∃ i, y ∈ interior (K i) := by
  classical
  let := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  have hlocal (y : C) : ∃ K : Set M, IsCompact K ∧ (y : M) ∈ interior K ∧
      K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (y : M)).source :=
    exists_compact_subset (chartAt (EuclideanSpace ℝ (Fin n)) (y : M)).open_source
      (mem_chart_source _ (y : M))
  choose K₀ hK₀ hK₀int hK₀s using hlocal
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun y : C => interior (K₀ y))
    (fun _ => isOpen_interior) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hK₀int ⟨y, hy⟩⟩)
  let e : Fin s.card ≃ s := s.equivFin.symm
  refine ⟨s.card, fun i => ((e i).1 : M), fun i => K₀ (e i).1,
    fun i => hK₀ (e i).1, fun i => hK₀s (e i).1, ?_⟩
  intro y hy
  obtain ⟨z, hzs, hz⟩ := mem_iUnion₂.mp (hs hy)
  refine ⟨e.symm ⟨z, hzs⟩, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hz

theorem m65FlowChartMetric_uniform_lower (p : M)
    {K : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKdomain : K ⊆ Ioo a b ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ z ∈ K, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ ≤ L * Real.sqrt (m65FlowChartMetric F p z w w) := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := K ×ˢ Metric.sphere (0 : E) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hG : ContinuousOn (fun z : (ℝ × E) × E => m65FlowChartMetric F p z.1) S :=
    (m65FlowChartMetric_contDiffOn F p).continuousOn.comp continuousOn_fst
      (fun _ hz => hKdomain hz.1)
  have hf : ContinuousOn (fun z : (ℝ × E) × E =>
      Real.sqrt (m65FlowChartMetric F p z.1 z.2 z.2)) S :=
    ((hG.clm_apply continuousOn_snd).clm_apply continuousOn_snd).sqrt
  have hpos (z : (ℝ × E) × E) (hz : z ∈ S) :
      0 < Real.sqrt (m65FlowChartMetric F p z.1 z.2 z.2) := by
    apply Real.sqrt_pos.mpr
    apply M04.shiChartMetric_pos (F.metric z.1.1)
      contMDiffOn_chart contMDiffOn_chart_symm (hKdomain hz.1).2
    have hn : ‖z.2‖ = 1 := mem_sphere_zero_iff_norm.mp hz.2
    intro he
    rw [he, norm_zero] at hn
    norm_num at hn
  obtain ⟨δ, hδ, hδbound⟩ := hS.exists_forall_le' hf hpos
  refine ⟨max 1 (1 / δ), le_max_left _ _, ?_⟩
  intro z hz v
  by_cases hv : v = 0
  · simp [hv]
  let w : E := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv
  have hrep : ‖v‖ • w = v := by
    simp only [w, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hδw := hδbound (z, w) ⟨hz, mem_sphere_zero_iff_norm.mpr hw⟩
  have hdiag : m65FlowChartMetric F p z v v =
      ‖v‖ ^ 2 * m65FlowChartMetric F p z w w := by
    calc
      _ = m65FlowChartMetric F p z (‖v‖ • w) (‖v‖ • w) := by rw [hrep]
      _ = _ := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
  have hroot : Real.sqrt (m65FlowChartMetric F p z v v) =
      ‖v‖ * Real.sqrt (m65FlowChartMetric F p z w w) := by
    rw [hdiag, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hnorm : ‖v‖ ≤ Real.sqrt (m65FlowChartMetric F p z v v) / δ := by
    apply (le_div_iff₀ hδ).mpr
    rw [hroot]
    nlinarith [mul_le_mul_of_nonneg_left hδw (norm_nonneg v)]
  calc
    ‖v‖ ≤ Real.sqrt (m65FlowChartMetric F p z v v) / δ := hnorm
    _ = (1 / δ) * Real.sqrt (m65FlowChartMetric F p z v v) := by ring
    _ ≤ max 1 (1 / δ) * Real.sqrt (m65FlowChartMetric F p z v v) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

theorem m65VerticalPairing_abs_le {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (t : ℝ) (q : P.charts.Point)
    (V : TangentSpace (𝓡 (n + 1)) q) :
    |(P.flow.metric t).inner q V (P.charts.circleUnit q)| ≤
      (P.flow.metric t).tangentNorm q V := by
  have hh : 0 ≤ (F.metric t).inner q.1
      (P.charts.split q V).1 (P.charts.split q V).1 :=
    ((F.metric t).toRiemannianMetric.toCore q.1).re_inner_nonneg _
  rw [m65Projection_inner_self P t q V] at hh
  unfold RiemannianMetric.tangentNorm
  rw [← Real.sqrt_sq_eq_abs ((P.flow.metric t).inner q V (P.charts.circleUnit q))]
  exact Real.sqrt_le_sqrt (sub_nonneg.mp hh)

theorem m65IntrinsicChartField_uniform_zero [T2Space M] {κ : Type*}
    {circumference : κ → ℝ} (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point) (p : M) {r s : ℝ}
    (hsub : Icc r s ⊆ Ioo a b) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      ((P k).flow.metric t).tangentNorm (c k x t)
        (m65IntrinsicTangentJet (P k).flow (c k) j t x) ≤ B) :
    ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s → (c k x t).1 ∈ K →
      ‖m65IntrinsicChartField (P k) (c k) p j t x‖ ≤ B := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hH : IsCompact (e '' K) :=
    hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hHt : e '' K ⊆ e.target := by
    rintro y ⟨q, hq, rfl⟩
    exact e.map_source (hKs hq)
  have hD : IsCompact (Icc r s ×ˢ (e '' K)) := isCompact_Icc.prod hH
  obtain ⟨L, hL, hLbound⟩ := m65FlowChartMetric_uniform_lower (F := F) p hD
    (fun _ hz => ⟨hsub hz.1, hHt hz.2⟩)
  intro j
  cases j with
  | zero =>
    have hswap : Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (z.2, z.1)) :=
      continuous_snd.prodMk continuous_fst
    obtain ⟨B, hB⟩ := (hD.image hswap).isBounded.exists_norm_le
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro k t x ht hx
    exact (hB _ ⟨(t, e (c k x t).1), ⟨ht, ⟨_, hx, rfl⟩⟩, rfl⟩).trans
      (le_max_right _ _)
  | succ j =>
    obtain ⟨B, hB, hb⟩ := hbound j
    refine ⟨L * B, mul_nonneg (zero_le_one.trans hL) hB, ?_⟩
    intro k t x ht hx
    change max ‖m65ProjectedCoordinateJet (P k) (c k) p j t x‖
      ‖((P k).flow.metric t).inner (c k x t)
        (m65IntrinsicTangentJet (P k).flow (c k) j t x)
        ((P k).charts.circleUnit (c k x t))‖ ≤ L * B
    apply max_le
    · have h := hLbound (t, e (c k x t).1) ⟨ht, ⟨_, hx, rfl⟩⟩
        (m65ProjectedCoordinateJet (P k) (c k) p j t x)
      rw [m65ProjectedCoordinateJet,
        m65FlowChartMetric_at_source F p t (hKs hx)] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        ((m65Projection_tangentNorm_le (P k) t _ _).trans (hb k t x ht))
        (zero_le_one.trans hL))
    · change ‖((P k).flow.metric t).inner (c k x t)
          (m65IntrinsicTangentJet (P k).flow (c k) j t x)
          ((P k).charts.circleUnit (c k x t))‖ ≤ L * B
      rw [Real.norm_eq_abs]
      exact ((m65VerticalPairing_abs_le (P k) t _ _).trans (hb k t x ht)).trans
        (le_mul_of_one_le_left hB hL)

end PoincareConjecture
