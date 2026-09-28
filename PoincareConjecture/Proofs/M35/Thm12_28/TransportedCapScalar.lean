import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarConvergence
import PoincareConjecture.Proofs.M35.Thm12_28.CapCompactness

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem ratio_stable {a B C delta u v U V : ℝ}
    (hB : 0 ≤ B) (hBC : B ≤ C) (hdelta : delta ≤ a / 2)
    (hgap : 2 * (B + 1) * delta ≤ (C - B) * a)
    (hfloor : a ≤ U) (hratio : V ≤ B * U)
    (hu : |u - U| < delta) (hv : |v - V| < delta) : v ≤ C * u := by
  obtain ⟨hu₁, hu₂⟩ := abs_lt.mp hu
  obtain ⟨hv₁, hv₂⟩ := abs_lt.mp hv
  have hlow : a / 2 ≤ u := by linarith
  have hupp : U ≤ u + delta := by linarith
  have hmul := mul_le_mul_of_nonneg_left hupp hB
  have hmargin := mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr hBC)
  nlinarith

theorem blowupSequence_cap_scalar_control (P : M35StandardCapPredecessors)
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
      ∃ a b B : ℝ, 0 < a ∧ 0 < b ∧ 0 < B ∧ B < N.cap_constant ∧
        ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀,
          let R : L.limit.sliceCarrier.carrier → ℝ := fun y =>
            (E.flow.connection (t (L.subsequence k))).scalarCurvature
              (((L.embedding k).forward 0
                ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val)
          let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
          (∀ y ∈ closure N.carrier, a * Q ≤ R y ∧ R y ≤ b * Q) ∧
          ∀ y ∈ closure N.carrier, ∀ z ∈ closure N.carrier, R z ≤ B * R y := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro N hconnection hcompact hU
  have hcont : Continuous N.connection.scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature N.connection).continuous
  obtain ⟨a, b, ha, hb, hbounds⟩ := N.exists_positive_scalar_bounds_on_closure hcont
  obtain ⟨B, hB, hBC, hratio⟩ := N.scalar_ratio_on_closure hcont
  obtain ⟨B', hBB', hB'C⟩ := exists_between hBC
  have hden : 0 < 2 * (B + 1) := by positivity
  let delta := min (a / 2) ((B' - B) * a / (2 * (B + 1)))
  have hdelta : 0 < delta := lt_min (by positivity)
    (div_pos (mul_pos (sub_pos.mpr hBB') ha) hden)
  have hdeltaA : delta ≤ a / 2 := min_le_left _ _
  have hdeltaB : 2 * (B + 1) * delta ≤ (B' - B) * a := by
    have h := (le_div_iff₀ hden).mp (min_le_right (a / 2) ((B' - B) * a / (2 * (B + 1))))
    exact (mul_comm _ _).trans_le h
  obtain ⟨k₀, hjk₀, hcompare⟩ := blowupSequence_terminal_scalar_uniform_compact
    P E t x ht hR L j (closure N.carrier) hcompact hU delta hdelta
  refine ⟨a / 2, b + delta, B', by positivity, by positivity, hB.trans hBB', hB'C,
    k₀, hjk₀, ?_⟩
  intro k hk
  let R : L.limit.sliceCarrier.carrier → ℝ := fun y =>
    (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val)
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (L.embedding k).scale_pos
  have herr (y : L.limit.sliceCarrier.carrier) (hy : y ∈ closure N.carrier) :
      |R y / Q - N.connection.scalarCurvature y| < delta := by
    have h := hcompare k hk y hy
    have heq := congrArg (fun D : LeviCivitaData (L.limit.flow.metric 0) =>
      D.scalarCurvature y) hconnection
    exact (congrArg (fun z : ℝ => |R y / Q - z| < delta) heq).mpr h
  constructor
  · intro y hy
    obtain ⟨hylo, hyhi⟩ := hbounds y hy
    obtain ⟨he₁, he₂⟩ := abs_lt.mp (herr y hy)
    have hlo : a / 2 ≤ R y / Q := by linarith
    have hhi : R y / Q ≤ b + delta := by linarith
    exact ⟨(le_div_iff₀ hQ).mp hlo, (div_le_iff₀ hQ).mp hhi⟩
  · intro y hy z hz
    have hnorm := ratio_stable hB.le hBB'.le hdeltaA hdeltaB
      (hbounds y hy).1 (hratio y hy z hz) (herr y hy) (herr z hz)
    apply (div_le_div_iff_of_pos_right hQ).mp
    simpa only [mul_div_assoc] using hnorm

end PoincareConjecture.M35.OrdinaryRealization
