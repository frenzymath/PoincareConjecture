import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarConvergence









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem sup_image_div_close {X Y : Type*} {U : Set X} (hU : U.Nonempty)
    (R : X → ℝ) (S : Y → ℝ) (f : X → Y) (hR : BddAbove (R '' U))
    {Q delta : ℝ} (hQ : 0 < Q) (herr : ∀ y ∈ U, |S (f y) / Q - R y| ≤ delta) :
    |sSup (S '' (f '' U)) / Q - sSup (R '' U)| ≤ delta := by
  have hpoint (y : X) (hy : y ∈ U) : R y ≤ sSup (R '' U) :=
    le_csSup hR (mem_image_of_mem R hy)
  have hupper : ∀ z ∈ S '' (f '' U), z ≤ (sSup (R '' U) + delta) * Q := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    apply (div_le_iff₀ hQ).mp
    have h := (abs_le.mp (herr y hy)).2
    linarith [hpoint y hy]
  have hS : BddAbove (S '' (f '' U)) := ⟨_, hupper⟩
  have hu : sSup (S '' (f '' U)) / Q ≤ sSup (R '' U) + delta :=
    (div_le_iff₀ hQ).mpr (csSup_le ((hU.image f).image S) hupper)
  have hl : sSup (R '' U) ≤ sSup (S '' (f '' U)) / Q + delta := by
    apply csSup_le (hU.image R)
    rintro _ ⟨y, hy, rfl⟩
    have hvalue : S (f y) / Q ≤ sSup (S '' (f '' U)) / Q :=
      div_le_div_of_nonneg_right
        (le_csSup hS (mem_image_of_mem S (mem_image_of_mem f hy))) hQ.le
    have h := (abs_le.mp (herr y hy)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩




theorem blowupSequence_scalar_sup_tendsto (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ)
    (U : Set L.limit.sliceCarrier.carrier) (hU : U.Nonempty)
    (hcompact : IsCompact (closure U)) (hUj : closure U ⊆ L.exhaustion.space j) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    Tendsto (fun k =>
      let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
        (E.flow.connection (t (L.subsequence k))) (f '' U) /
          (blowupSequence P E t x ht hR).scale (L.subsequence k)) atTop
      (𝓝 (scalarCurvatureSupOn (L.limit.flow.metric 0) (L.limit.flow.connection 0) U)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have hcont : Continuous (L.limit.flow.connection 0).scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (L.limit.flow.connection 0)).continuous
  have hbounded : BddAbove ((L.limit.flow.connection 0).scalarCurvature '' U) :=
    (hcompact.bddAbove_image hcont.continuousOn).mono (image_mono subset_closure)
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  obtain ⟨k₀, _, herr⟩ := blowupSequence_terminal_scalar_uniform_compact
    P E t x ht hR L j (closure U) hcompact hUj (delta / 2) (by positivity)
  refine ⟨k₀, ?_⟩
  intro k hk
  let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun z => ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  have hsup := sup_image_div_close hU (L.limit.flow.connection 0).scalarCurvature
    (E.flow.connection (t (L.subsequence k))).scalarCurvature f hbounded
    (L.embedding k).scale_pos (fun y hy => (herr k hk y (subset_closure hy)).le)
  have hsmall := hsup.trans_lt (half_lt_self hdelta)
  have hsource : scalarCurvatureSupOn (L.limit.flow.metric 0)
      (L.limit.flow.connection 0) U =
        sSup ((L.limit.flow.connection 0).scalarCurvature '' U) :=
    congrArg sSup (image_eq_range (L.limit.flow.connection 0).scalarCurvature U).symm
  have htarget : scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
      (E.flow.connection (t (L.subsequence k))) (f '' U) =
        sSup ((E.flow.connection (t (L.subsequence k))).scalarCurvature '' (f '' U)) :=
    congrArg sSup (image_eq_range
      (E.flow.connection (t (L.subsequence k))).scalarCurvature (f '' U)).symm
  rw [Real.dist_eq]
  change |scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
      (E.flow.connection (t (L.subsequence k))) (f '' U) /
        (blowupSequence P E t x ht hR).scale (L.subsequence k) -
          scalarCurvatureSupOn (L.limit.flow.metric 0) (L.limit.flow.connection 0) U| < delta
  rw [hsource, htarget]
  exact hsmall

end PoincareConjecture.M35.OrdinaryRealization
