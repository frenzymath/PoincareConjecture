import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCurvatureDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_terminal_curvature_derivative_bounded_chart
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ)
    (K : Set V) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j}) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
    let hQ k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
    let phi k z := ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
    ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ p ∈ K,
      (M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k)))
        (Q k) (hQ k)).curvatureDerivativeNorm 1 (phi k ((extChartAt (𝓡 3) q).symm p)) ≤ B := by
  classical
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let hQ k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let phi k z := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let F (k : ℕ) (p : V) :=
    (M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k)))
      (Q k) (hQ k)).curvatureDerivativeNorm 1 (phi k (c.symm p))
  change ∃ B : ℝ, 0 < B ∧ ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ p ∈ K, F k p ≤ B
  by_contra hnot
  push Not at hnot
  have hbad : ∀ n : ℕ, ∃ k ≥ n, ∃ p ∈ K, (n : ℝ) + 1 < F k p := by
    intro n
    obtain ⟨k, hk, p, hp, hlarge⟩ := hnot ((n : ℝ) + 1) (by positivity)
      (max j n) (le_max_left _ _)
    exact ⟨k, (le_max_right j n).trans hk, p, hp, hlarge⟩
  choose k hk p hp hlarge using hbad
  obtain ⟨z, hz, sigma, hsigma, hlim⟩ := hK.tendsto_subseq hp
  have hindex : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hnorm := blowupSequence_terminal_curvature_derivative_tendsto_chart
    P E t x ht hR L q j K hK hKU (k ∘ sigma) (hindex.comp hsigma.tendsto_atTop)
    (p ∘ sigma) (fun n => hp (sigma n)) z hz hlim
  let B := (L.limit.flow.connection 0).curvatureDerivativeNorm 1 (c.symm z)
  have hnorm' : Tendsto (fun n => F (k (sigma n)) (p (sigma n))) atTop (𝓝 B) := hnorm
  have hupper := hnorm'.eventually (eventually_lt_nhds (lt_add_one B))
  have hcast : Tendsto (fun n => (sigma n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hsigma.tendsto_atTop
  obtain ⟨n, hnupper, hnlower⟩ :=
    (hupper.and (hcast.eventually (eventually_gt_atTop B))).exists
  have h := hlarge (sigma n)
  linarith

end PoincareConjecture.M35.OrdinaryRealization
