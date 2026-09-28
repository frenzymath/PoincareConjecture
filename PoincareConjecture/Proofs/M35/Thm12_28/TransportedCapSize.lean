import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapDiameter
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapVolume
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapScalar
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedScalarSup










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem size_normalization {Q S T : ℝ} (hQ : 0 < Q) (hS : 0 < S) (hT : 0 < T)
    (hupper : T ≤ 2 * Q * S) :
    Real.sqrt ((1 + 1 / 2) / Q) * S ^ (-1 / 2 : ℝ) ≤ 2 * T ^ (-1 / 2 : ℝ) ∧
      Real.sqrt ((1 + 1 / 2) / Q) ^ 3 * S ^ (-3 / 2 : ℝ) ≤
        8 * T ^ (-3 / 2 : ℝ) := by
  let m := Real.sqrt ((1 + 1 / 2) / Q)
  have hm : 0 ≤ m := Real.sqrt_nonneg _
  have hmsq : m ^ 2 * Q = 3 / 2 := by
    rw [Real.sq_sqrt (div_nonneg (by norm_num) hQ.le), div_mul_cancel₀ _ hQ.ne']
    norm_num
  have hcompare : m * Real.sqrt T ≤ 2 * Real.sqrt S := by
    have hmul := mul_le_mul_of_nonneg_left hupper (sq_nonneg m)
    have hs := Real.sq_sqrt hS.le
    have ht := Real.sq_sqrt hT.le
    have hrel : m ^ 2 * T ≤ 3 * S := by
      nlinarith [congrArg (fun z : ℝ => z * S) hmsq]
    nlinarith [sq_nonneg (m * Real.sqrt T - 2 * Real.sqrt S),
      Real.sqrt_nonneg S, Real.sqrt_nonneg T]
  have hhalf (x : ℝ) (hx : 0 ≤ x) : x ^ (-1 / 2 : ℝ) = (Real.sqrt x)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hx, ← Real.sqrt_eq_rpow]
  have hfirst : m * S ^ (-1 / 2 : ℝ) ≤ 2 * T ^ (-1 / 2 : ℝ) := by
    rw [hhalf S hS.le, hhalf T hT.le, ← div_eq_mul_inv, ← div_eq_mul_inv]
    exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hS) (Real.sqrt_pos.mpr hT)).mpr hcompare
  have hthree (x : ℝ) (hx : 0 ≤ x) : x ^ (-3 / 2 : ℝ) = (x ^ (-1 / 2 : ℝ)) ^ 3 := by
    rw [show (-3 / 2 : ℝ) = (-1 / 2) * (3 : ℕ) by norm_num]
    exact Real.rpow_mul_natCast hx _ _
  refine ⟨hfirst, ?_⟩
  have hcube := pow_le_pow_left₀ (mul_nonneg hm (Real.rpow_nonneg hS.le _)) hfirst 3
  rw [mul_pow, mul_pow, ← hthree S hS.le, ← hthree T hT.le] at hcube
  simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num] using hcube




theorem blowupSequence_cap_size_bounds (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace :=
          fun z => ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        let R := scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
          (E.flow.connection (t (L.subsequence k))) (f '' N.carrier)
        intrinsicDiameter (E.flow.metric (t (L.subsequence k))) (f '' N.carrier) <
          ENNReal.ofReal (2 * N.cap_constant * R ^ (-1 / 2 : ℝ)) ∧
        calibratedMetricVolume (E.flow.metric (t (L.subsequence k))) (f '' N.carrier) <
          ENNReal.ofReal (8 * N.cap_constant * R ^ (-3 / 2 : ℝ)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro N hconnection hcompact hU
  obtain ⟨y, hy⟩ := N.core_nonempty
  have hyU : y ∈ N.carrier := by
    have hc := N.core_eq_interior_closed_core ▸ hy
    exact (N.closed_core_eq_complement_end ▸ interior_subset hc).1
  have hnonempty : N.carrier.Nonempty := ⟨y, hyU⟩
  have hcont : Continuous N.connection.scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature N.connection).continuous
  obtain ⟨a, b, _, _, hbounds⟩ := N.exists_positive_scalar_bounds_on_closure hcont
  let S := scalarCurvatureSupOn (L.limit.flow.metric 0) N.connection N.carrier
  have hS : 0 < S := by
    apply (N.scalar_pos y hyU).trans_le
    apply le_csSup (a := N.connection.scalarCurvature y)
      (show BddAbove (range fun z : N.carrier => N.connection.scalarCurvature z) from ?_)
      ⟨⟨y, hyU⟩, rfl⟩
    refine ⟨b, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (hbounds z (subset_closure z.property)).2
  let f (k : ℕ) : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun z => ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let R (k : ℕ) := scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
    (E.flow.connection (t (L.subsequence k))) (f k '' N.carrier)
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hlim : Tendsto (fun k => R k / Q k) atTop (𝓝 S) := by
    simpa only [S, hconnection] using
      blowupSequence_scalar_sup_tendsto P E t x ht hR L j N.carrier hnonempty hcompact hU
  have hgood : ∀ᶠ k in atTop, 0 < R k / Q k ∧ R k / Q k < 2 * S :=
    hlim.eventually (inter_mem (eventually_gt_nhds hS)
      (eventually_lt_nhds (by linarith : S < 2 * S)))
  obtain ⟨ks, hks⟩ := eventually_atTop.mp hgood
  obtain ⟨kd, _, hdiam⟩ := blowupSequence_cap_diameter_bound
    P E t x ht hR L j (1 / 2) (by norm_num) N hcompact hU
  obtain ⟨kv, _, hvolume⟩ := blowupSequence_cap_volume_bound
    P E t x ht hR L j (eta := 1 / 2) (by norm_num) (by norm_num) N hcompact hU
  refine ⟨max j (max ks (max kd kv)), le_max_left _ _, ?_⟩
  intro k hk
  have hkS : ks ≤ k := by omega
  have hkD : kd ≤ k := by omega
  have hkV : kv ≤ k := by omega
  have hQ : 0 < Q k := (L.embedding k).scale_pos
  have hRpos : 0 < R k := by
    have h := (lt_div_iff₀ hQ).mp (hks k hkS).1
    simpa only [zero_mul] using h
  have hRupper : R k ≤ 2 * Q k * S := by
    have h := (div_lt_iff₀ hQ).mp (hks k hkS).2
    nlinarith
  obtain ⟨hsize, hsize3⟩ := size_normalization hQ hS hRpos hRupper
  constructor
  · refine (hdiam k hkD).trans_le (ENNReal.ofReal_le_ofReal ?_)
    change Real.sqrt ((1 + 1 / 2) / Q k) * (N.cap_constant * S ^ (-1 / 2 : ℝ)) ≤
      2 * N.cap_constant * R k ^ (-1 / 2 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hsize N.cap_constant_pos.le]
  · have hv := hvolume k hkV
    change calibratedMetricVolume (E.flow.metric (t (L.subsequence k))) (f k '' N.carrier) <
      ENNReal.ofReal (Real.sqrt ((1 + 1 / 2) / Q k) ^ 3) *
        (ENNReal.ofReal N.cap_constant * ENNReal.ofReal (S ^ (-3 / 2 : ℝ))) at hv
    rw [← ENNReal.ofReal_mul N.cap_constant_pos.le,
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) 3)] at hv
    refine hv.trans_le (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [mul_le_mul_of_nonneg_left hsize3 N.cap_constant_pos.le]

end PoincareConjecture.M35.OrdinaryRealization
