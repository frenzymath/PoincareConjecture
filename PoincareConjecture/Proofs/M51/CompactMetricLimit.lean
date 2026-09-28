import PoincareConjecture.Proofs.M51.MetricLimitJets










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M51

variable {A : GeneralizedSliceCarrier.{u}}



theorem metricLimit_local_curvature_bound
    (g : ℝ → RiemannianMetric 3 A.carrier) (D : ∀ t, LeviCivitaData (g t))
    (g₀ : RiemannianMetric 3 A.carrier) {T : ℝ}
    (hlim : SurgeryMetricLimitOn A A g g₀ id univ T) (q : A.carrier) :
    ∃ U ∈ 𝓝 q, ∃ d > 0, ∃ L ≥ 0,
      ∀ t ∈ Ioo (T - d) T, ∀ x ∈ U, (D t).curvatureTensorNorm x ≤ L := by
  let c := extChartAt (𝓡 3) q
  let p : c.target := ⟨c q, mem_extChartAt_target q⟩
  obtain ⟨r, hr, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds p.2)
  let K := Metric.closedBall p.1 r
  let l : Filter (ℝ × c.target) := (𝓝[<] T) ×ˢ 𝓝 p
  have hcoord : Tendsto (fun i : ℝ × c.target => i.2.1) l (𝓝[K] p.1) := by
    rw [nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds _ hr)]
    exact continuous_subtype_val.continuousAt.tendsto.comp tendsto_snd
  obtain ⟨L, hL, hconv⟩ := curvatureNorm_limit_of_chart_jets
    (fun i : ℝ × c.target => g i.1) (fun i => D i.1) g₀ q (fun i => i.2.1)
    (fun i => i.2.2) p.1 p.2 (fun k _ a b =>
      metricLimit_jets_tendsto g g₀ hlim q (isCompact_closedBall p.1 r) hK
        (l := l) tendsto_fst (Metric.mem_closedBall_self hr.le) hcoord k a b)
  have hbound : ∀ᶠ i : ℝ × c.target in l,
      (D i.1).curvatureTensorNorm (c.symm i.2.1) ≤ L + 1 := by
    have hlt : ∀ᶠ i : ℝ × c.target in l,
        (D i.1).curvatureTensorNorm (c.symm i.2.1) < L + 1 :=
      hconv (Iio_mem_nhds (show L < L + 1 by linarith))
    exact hlt.mono fun _ hi => hi.le
  obtain ⟨pa, hpa, pb, hpb, hproduct⟩ := eventually_prod_iff.mp hbound
  obtain ⟨s, hs, htime⟩ := (nhdsLT_basis T).mem_iff.mp hpa
  obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype c.target p {y | pb y}).mp hpb
  let U := c.source ∩ c ⁻¹' (c.target ∩ V)
  have hU : U ∈ 𝓝 q := by
    apply inter_mem
    · exact (isOpen_extChartAt_source q).mem_nhds (mem_extChartAt_source q)
    · have hc : ContinuousAt c q :=
        continuousAt_extChartAt (I := 𝓡 3) q
      exact hc (inter_mem ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds p.2) hV)
  refine ⟨U, hU, T - s, sub_pos.mpr hs, L + 1, by linarith, ?_⟩
  intro t ht x hx
  have hts : t ∈ Ioo s T := by constructor <;> linarith [ht.1, ht.2]
  have hb := hproduct (htime hts) (hVsub (show (⟨c x, hx.2.1⟩ : c.target) ∈
    Subtype.val ⁻¹' V from hx.2.2))
  simpa only [c.left_inv hx.1] using hb


theorem metricLimit_curvature_bound_of_compact
    (g : ℝ → RiemannianMetric 3 A.carrier) (D : ∀ t, LeviCivitaData (g t))
    (g₀ : RiemannianMetric 3 A.carrier) {T : ℝ}
    (hA : IsCompact (univ : Set A.carrier))
    (hlim : SurgeryMetricLimitOn A A g g₀ id univ T) :
    ∃ d > 0, ∃ L ≥ 0,
      ∀ t ∈ Ioo (T - d) T, ∀ x, (D t).curvatureTensorNorm x ≤ L := by
  classical
  choose U hU d hd L hL hb using metricLimit_local_curvature_bound g D g₀ hlim
  obtain ⟨s, _, hcover⟩ := hA.elim_nhds_subcover U (fun x _ => hU x)
  have hfinite : ∀ s : Finset A.carrier,
      ∃ d₀ > 0, ∃ L₀ ≥ 0, ∀ x ∈ s, d₀ ≤ d x ∧ L x ≤ L₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, 0, le_rfl, by simp⟩
    | @insert x s hxs ih =>
      obtain ⟨d₀, hd₀, L₀, hL₀, hs⟩ := ih
      refine ⟨min d₀ (d x), lt_min hd₀ (hd x), max L₀ (L x),
        hL₀.trans (le_max_left _ _), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨min_le_right _ _, le_max_right _ _⟩
      · exact ⟨(min_le_left _ _).trans (hs y hy).1,
          (hs y hy).2.trans (le_max_left _ _)⟩
  obtain ⟨d₀, hd₀, L₀, hL₀, hs⟩ := hfinite s
  refine ⟨d₀, hd₀, L₀, hL₀, ?_⟩
  intro t ht x
  obtain ⟨q, hq, hx⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  exact (hb q t ⟨by linarith [(hs q hq).1, ht.1], ht.2⟩ x hx).trans (hs q hq).2

end PoincareConjecture.M51

namespace PoincareConjecture.SurgeryMetricLimitOn



theorem curvature_bound_of_compact
    (A B : GeneralizedSliceCarrier.{u})
    (g : ℝ → RiemannianMetric 3 A.carrier) (D : ∀ t, LeviCivitaData (g t))
    (gT : RiemannianMetric 3 B.carrier)
    (f : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (T : ℝ) (hA : IsCompact (univ : Set A.carrier))
    (hlim : SurgeryMetricLimitOn A B g gT f univ T) :
    ∃ d > 0, ∃ L ≥ 0,
      ∀ t ∈ Ioo (T - d) T, ∀ x, (D t).curvatureTensorNorm x ≤ L :=
  M51.metricLimit_curvature_bound_of_compact g D
    (gT.pullbackOfLocalDiffeomorph f f.isLocalDiffeomorph) hA
    (M51.surgeryMetricLimitOn_pullback g gT f hlim)

end PoincareConjecture.SurgeryMetricLimitOn
