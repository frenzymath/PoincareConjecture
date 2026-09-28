import PoincareConjecture.Proofs.M35.CapGeometry.UnitTimeCanonical











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization




theorem exists_bounded_tip_cap_threshold_of_selected
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (epsilon D : ℝ)
    (hselected : ∀ (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
      (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
      (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k))
        atTop atTop),
      (∀ k, ((E.flow.metric (t k)).edist 0 (x k)).toReal *
        Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)) ≤ D) →
      ∀ (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
        (blowupBackwardInterval ⊤)) (kappa : ℝ),
      BlowupAncientKappaIdentification L.limit kappa →
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ k in atTop, ∀ C ≥ C₀,
        Nonempty (StandardCapNeighborhood E.atlas E.flow
          (t (L.subsequence k)) epsilon C (x (L.subsequence k)))) :
    ∃ C₀ H : ℝ, 0 < C₀ ∧ 0 < H ∧ ∀ C ≥ C₀,
      ∀ t, ∀ _ht : t ∈ Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
        H ≤ (E.flow.connection t).scalarCurvature x →
        ((E.flow.metric t).edist 0 x).toReal *
          Real.sqrt ((E.flow.connection t).scalarCurvature x) ≤ D →
        Nonempty (StandardCapNeighborhood E.atlas E.flow t epsilon C x) := by
  classical
  obtain ⟨delta, hdelta, hcanonical⟩ := exists_unit_time_canonical_constants P
  obtain ⟨deltaA, hdeltaA, hextract⟩ := exists_ancient_extraction_threshold P
  let eta := min delta deltaA
  have heta : 0 < eta := lt_min hdelta hdeltaA
  obtain ⟨Cunit, H, hCunit, hH, hgood⟩ :=
    hcanonical eta heta (min_le_left _ _) E
  by_contra hnone
  push Not at hnone
  have hselect (k : ℕ) := hnone ((k : ℝ) + 1) (H + (k : ℝ) + 1)
    (by positivity) (by positivity)
  choose C hC t ht x hscalar hdistance hbad using hselect
  have hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k))
      atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (b - H - 1)] with k hk
    linarith [hscalar k]
  have hconstants : Tendsto C atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (b - 1)] with k hk
    linarith [hC k]
  have hprior : ∀ k, generalizedEarlierStrongCanonicalNeighborhoods
      ((blowupSequence P E t x ht hR).flow k) eta Cunit
      ((blowupSequence P E t x ht hR).base k).1
      ((blowupSequence P E t x ht hR).base k).2 := by
    intro k s hs _hst y hhigh
    have hscale := scalar_eq P E.flow.base.flow (ht k) (x k)
    have hvalue := scalar_eq P E.flow.base.flow hs y.val
    have hhigh' : 4 * (E.flow.connection (t k)).scalarCurvature (x k) ≤
        (E.flow.connection s).scalarCurvature y.val :=
      (congrArg (fun r : ℝ => 4 * r) hscale).symm ▸ (hvalue ▸ hhigh)
    have hthreshold : H ≤ (E.flow.connection s).scalarCurvature y.val := by
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith only [hH, hscalar k, hk, hhigh']
    exact ⟨hgood s hs y.val hthreshold⟩
  obtain ⟨kappa, _hkappa, L, ⟨A⟩⟩ :=
    hextract eta Cunit heta (min_le_right _ _) hCunit g₀ E t x ht hR hprior
  obtain ⟨C₀, _hC₀, hcap⟩ := hselected t x ht hR hdistance L kappa A.certificate
  have hlarge : ∀ᶠ k in atTop, C₀ ≤ C (L.subsequence k) :=
    (hconstants.comp L.subsequence_strictMono.tendsto_atTop).eventually_ge_atTop C₀
  obtain ⟨k, hk, hc⟩ := (hcap.and hlarge).exists
  exact (hbad (L.subsequence k)).false (hk (C (L.subsequence k)) hc).some

end PoincareConjecture.M35.OrdinaryRealization
