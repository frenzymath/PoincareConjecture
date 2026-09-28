import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitConstruction











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "V" => MetricCoefficient 3

noncomputable local instance rescaledLimitClosedJetsCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rescaledLimitClosedJetsCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace




theorem tendstoUniformlyOn_spatialJet_of_compactSmooth
    {fseq : ℕ → ℝ × E → V} {b : ℝ × E → V} {U : Set (ℝ × E)}
    (h : CompactSmoothConvergenceOn fseq b atTop U)
    (m : ℕ) {K : Set (ℝ × E)} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (fun x => fseq k (p.1, x)) p.2)
      (fun p => iteratedFDeriv ℝ m (fun x => b (p.1, x)) p.2) atTop K := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := V) (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E)
  have hfull := P.uniformContinuous.comp_tendstoUniformlyOn (h.jets m K hK hKU)
  apply (hfull.congr ?_).congr_right ?_
  · filter_upwards [h.eventually_smooth K hK hKU] with k hk
    intro p hp
    apply ContinuousMultilinearMap.ext
    intro v
    exact (Poincare.Analysis.iteratedFDeriv_spatial_slice (fseq k) (hk p hp) m v).symm
  · intro p hp
    apply ContinuousMultilinearMap.ext
    intro v
    exact (Poincare.Analysis.iteratedFDeriv_spatial_slice b
      (h.smooth.contDiffAt (h.isOpen.mem_nhds (hKU hp))) m v).symm

set_option maxHeartbeats 800000 in







theorem tendstoUniformlyOn_rescaled_spatialJets_closed_birth
    {fseq : ℕ → ℝ × E → V} {b : ℝ × E → V} {T T0 : ℝ}
    (hT0 : 0 ≤ T0) (hT0T : T0 < T)
    (hconv : CompactSmoothConvergenceOn fseq b atTop (Ioo 0 T ×ˢ univ))
    (m : ℕ) {K : Set E} (hK : IsCompact K)
    (hbirth : TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x)
      (fun x => iteratedFDeriv ℝ m (fun y => b (0, y)) x) atTop K)
    (hmodulus : ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Ioo 0 T, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => fseq k (t, y)) x -
          iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x‖ ≤ L * t) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (fun y => fseq k (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ m (fun y => b (p.1, y)) p.2) atTop (Icc 0 T0 ×ˢ K) := by
  let A (k : ℕ) (p : ℝ × E) := iteratedFDeriv ℝ m (fun y => fseq k (p.1, y)) p.2
  let B (p : ℝ × E) := iteratedFDeriv ℝ m (fun y => b (p.1, y)) p.2
  have hT : 0 < T := hT0.trans_lt hT0T
  obtain ⟨L, hL, hmod⟩ := hmodulus
  have hlimit (t : ℝ) (ht : t ∈ Ico 0 T) (x : E) (hx : x ∈ K) :
      dist (B (t, x)) (B (0, x)) ≤ L * t := by
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · subst t
      simp only [dist_self, mul_zero, le_refl]
    · rw [dist_eq_norm]
      exact le_of_tendsto
        (((tendsto_spatialJet_of_compactSmooth hconv (p := (t, x))
          ⟨⟨hpos, ht.2⟩, mem_univ x⟩ m).sub (hbirth.tendsto_at hx)).norm)
        (hmod.mono fun k hk => hk t ⟨hpos, ht.2⟩ x hx)
  change TendstoUniformlyOn A B atTop (Icc 0 T0 ×ˢ K)
  rw [Metric.tendstoUniformlyOn_iff]
  intro eta heta
  have hL1 : 0 < L + 1 := by linarith
  let d := min (T / 2) ((eta / 6) / (L + 1))
  have hd : 0 < d := lt_min (half_pos hT) (div_pos (by positivity) hL1)
  have hstrip : Icc d T0 ×ˢ K ⊆ Ioo 0 T ×ˢ (univ : Set E) := by
    intro p hp
    exact ⟨⟨hd.trans_le hp.1.1, hp.1.2.trans_lt hT0T⟩, mem_univ _⟩
  have hinterior := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_spatialJet_of_compactSmooth hconv m
      (isCompact_Icc.prod hK) hstrip) eta heta
  have hbirth_eta := Metric.tendstoUniformlyOn_iff.mp hbirth (eta / 3) (by positivity)
  filter_upwards [hmod, hinterior, hbirth_eta] with k hk hki hk0
  rintro ⟨t, x⟩ ht
  by_cases hdt : d ≤ t
  · exact hki (t, x) ⟨⟨hdt, ht.1.2⟩, ht.2⟩
  · have htd : t < d := lt_of_not_ge hdt
    have hsmall : L * t < eta / 6 := by
      have hratio : t < (eta / 6) / (L + 1) := htd.trans_le (min_le_right _ _)
      have hmul := (lt_div_iff₀ hL1).mp hratio
      nlinarith [ht.1.1]
    have happrox : dist (A k (0, x)) (A k (t, x)) ≤ L * t := by
      rcases eq_or_lt_of_le ht.1.1 with hzero | hpos
      · change 0 = t at hzero
        subst t
        simp only [dist_self, mul_zero, le_refl]
      · rw [dist_comm, dist_eq_norm]
        exact hk t ⟨hpos, ht.1.2.trans_lt hT0T⟩ x ht.2
    have hlim := hlimit t ⟨ht.1.1, ht.1.2.trans_lt hT0T⟩ x ht.2
    have hbirth_bound := hk0 x ht.2
    have htriangle := (dist_triangle (B (t, x)) (B (0, x)) (A k (t, x))).trans
      (add_le_add le_rfl (dist_triangle (B (0, x)) (A k (0, x)) (A k (t, x))))
    change dist (B (t, x)) (A k (t, x)) < eta
    change dist (B (0, x)) (A k (0, x)) < eta / 3 at hbirth_bound
    linarith






theorem tendstoUniformlyOn_rescaled_partial_flow_closed_jets
    {g0 : StandardInitialMetric} (S : PartialStandardCapFlow g0)
    {fseq : ℕ → ℝ × E → V} {T T0 : ℝ}
    (hT0 : 0 ≤ T0) (hT0T : T0 < T)
    (hconv : CompactSmoothConvergenceOn fseq
      (fun p => (S.flow.metric p.1).euclideanCoefficients p.2) atTop
      (Ioo 0 T ×ˢ univ))
    (m : ℕ) {K : Set E} (hK : IsCompact K)
    (hbirth : TendstoUniformlyOn
      (fun k x => iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x)
      (iteratedFDeriv ℝ m g0.metric.euclideanCoefficients) atTop K)
    (hmodulus : ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Ioo 0 T, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y => fseq k (t, y)) x -
          iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x‖ ≤ L * t) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ m (fun y => fseq k (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ m (S.flow.metric p.1).euclideanCoefficients p.2)
      atTop (Icc 0 T0 ×ˢ K) := by
  apply tendstoUniformlyOn_rescaled_spatialJets_closed_birth hT0 hT0T hconv m hK
    (by simpa only [S.initial_metric] using hbirth) hmodulus

end PoincareConjecture.M44
