import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.ExteriorScalarPropagation
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.ExteriorPositiveVolume
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CompactCenterBall
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.SecondBlowupSequence
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.Chapter11Volume
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapLongControls
import PoincareConjecture.Proofs.M34.Standard.GeneralizedVolumeCollapse












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M34

variable {g0 : StandardInitialMetric} (F : MaximalStandardCapFlow g0)
  (P : M34StandardCapPredecessors)
  (R : OrdinaryProductRicciGeometry F.base.flow.metric (partialFlowSpacetimeInterval F.base))

local notation "G" => ordinaryChapter11Flow
  (I := partialFlowSpacetimeInterval F.base) (F := F.base.flow) R

include P




theorem standardFlow_lifetime_ge_one_of_good_points (E0 : StandardCapEstimate g0)
    (H : StandardFlowNoncollapsingCertificate F) {epsilon0 epsilon C A Rstar : ℝ}
    (long : M30LongLimitStatement.{0} epsilon0) (hepsilon : 0 < epsilon)
    (hepsilon0 : epsilon ≤ epsilon0) (hC : 0 < C) (hA : 0 < A)
    (hgood : ∀ p : (G).point, Rstar ≤ (G).scalar p →
      Chapter11GoodPoint (G) epsilon C A p) :
    1 ≤ F.base.lifetime := by
  by_contra hnot
  have hL : F.base.lifetime < 1 := lt_of_not_ge hnot
  obtain ⟨B, hB, _hRB, T0, hT0, X, hX, houtside⟩ :=
    partialFlow_exists_exterior_scalar_bound_of_good_points F.base P E0 R hA hL hgood
  have hcurv : ∀ t ∈ Ico T0 F.base.lifetime, ∀ x ∉ X,
      (F.base.flow.connection t).curvatureTensorNorm x ≤ 2 * B :=
    fun t ht x hx => (houtside t ht x hx).2.2
  obtain ⟨Omega, _hopen, _hne, hcompact, _hOmegaX, v, hv, hvolume⟩ :=
    partialFlow_exists_fixed_exterior_volume F.base P.curvature hT0 hB hX hcurv
  obtain ⟨D, hD, hball⟩ :=
    partialFlow_exists_compact_center_ball_radius F.base P.curvature E0 hX hcompact
  obtain ⟨p, hp, hdiverges⟩ :=
    standardFlow_chapter11_compact_center_sequence F P R E0 hT0 hcurv Rstar
  have hpositive (k : ℕ) : 0 < (G).scalar (p k) :=
    lt_trans (by positivity) (hp k).2.2.2
  let r0 := min H.radius (Real.sqrt (F.base.lifetime / 4))
  have htail : 0 < F.base.lifetime / 4 := div_pos F.base.lifetime_pos (by norm_num)
  have hr0 : 0 < r0 := lt_min H.radius_pos (Real.sqrt_pos.mpr htail)
  have hradius : r0 ≤ H.radius := min_le_left _ _
  have hrtime : r0 ^ 2 ≤ F.base.lifetime / 4 := calc
    r0 ^ 2 ≤ (Real.sqrt (F.base.lifetime / 4)) ^ 2 :=
      pow_le_pow_left₀ hr0.le (min_le_right _ _) _
    _ = F.base.lifetime / 4 := Real.sq_sqrt htail.le
  obtain ⟨controls⟩ := standardFlow_chapter11_long_controls F P R E0
    p hpositive hdiverges H hr0 hradius hrtime hepsilon hC hA (by
      intro k q _ hhigh
      apply hgood q
      linarith [(hp k).2.2.1, hpositive k])
  let S := fixedFlowBlowupSequence (G) p hpositive hdiverges
  obtain ⟨L⟩ := long S epsilon C H.kappa r0 1 ⊤ hepsilon0 controls
  let Conv := L.convergence
  let : TopologicalSpace Conv.limit.carrier.carrier := Conv.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Conv.limit.carrier.carrier :=
    Conv.limit.carrier.chartedSpace
  let : IsManifold (𝓡 3) ∞ Conv.limit.carrier.carrier := Conv.limit.carrier.isManifold
  let : MeasurableSpace Conv.limit.carrier.carrier := Conv.limit.carrier.measurableSpace
  let : BorelSpace Conv.limit.carrier.carrier := Conv.limit.carrier.borelSpace
  let : T2Space Conv.limit.carrier.carrier := Conv.limit.carrier.t2Space
  let : T3Space Conv.limit.carrier.carrier := Conv.limit.carrier.t3Space
  let : SecondCountableTopology Conv.limit.carrier.carrier := Conv.limit.carrier.secondCountable
  let : ConnectedSpace Conv.limit.carrier.carrier := Conv.limit.connectedSpace
  obtain ⟨Id⟩ := L.ancient rfl
  have hzero : asymptoticVolumeRatio (Conv.limit.flow.metric 0) Conv.limit.base = 0 := by
    have hz := P.zero_avr Id.certificate.solution 0 le_rfl Conv.limit.base
    rwa [Id.certificate.metric_eq 0 le_rfl] at hz
  have hBG : ∀ᶠ k : ℕ in atTop, AntitoneMetricBallVolumeRatio
      ((S.flow (Conv.subsequence k)).metric (S.base (Conv.subsequence k)).1)
        (S.base (Conv.subsequence k)).2 := Eventually.of_forall fun k =>
    partialFlow_chapter11_bishopGromov F.base P R E0 (p (Conv.subsequence k))
  obtain ⟨k, hk⟩ := (Conv.eventually_fixed_ball_volume_lt_of_zero_avr hzero hBG hD hv).exists
  let j := Conv.subsequence k
  change calibratedMetricVolume ((G).metric (p j).1)
    (((G).metric (p j).1).ball (p j).2 D) < ENNReal.ofReal v at hk
  rw [partialFlow_chapter11_ball_volume F.base P R (p j) D] at hk
  have htime := ordinaryChapter11Point_time_mem R (p j)
  have hlower := (hvolume (p j).1 ⟨(hp j).1.le, htime.2⟩).trans
    (measure_mono (hball (p j).1 htime (ordinaryChapter11Projection R (p j)) (hp j).2.1))
  exact (not_lt_of_ge hlower) hk

end PoincareConjecture.M34
