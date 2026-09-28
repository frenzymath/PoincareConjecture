import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapDistance
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCoordinates
import PoincareConjecture.Proofs.M35.CapGeometry.RadialNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => StandardCapSpace

theorem blowupSequence_selected_point_distance_bound
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → V)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (y : L.limit.sliceCarrier.carrier) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let G : RiemannianMetric 3 V :=
        M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
      let f (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      G.edist (x (L.subsequence k)) (f y) < ENNReal.ofReal B := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  have : LocallyCompactSpace L.limit.carrier.carrier :=
    ChartedSpace.locallyCompactSpace V L.limit.carrier.carrier
  let g : RiemannianMetric 3 L.limit.carrier.carrier := L.limit.flow.metric 0
  let d := (g.edist L.limit.base y).toReal + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdistance : g.edist L.limit.base y < ENNReal.ofReal d := by
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top _ _),
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
    dsimp only [d]
    linarith
  obtain ⟨gamma, hstart, hend, hsmooth, hlength⟩ :=
    M13.exists_pathELength_lt g hdistance
  have hcompact : IsCompact (gamma '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hsmooth.continuousOn
  obtain ⟨K, hK, hinside, _⟩ := exists_compact_between hcompact isOpen_univ (subset_univ _)
  obtain ⟨j, hstage⟩ := hK.elim_directed_cover L.exhaustion.space L.exhaustion.space_open
    (fun z _ => by rw [L.exhaustion.space_covers]; exact mem_univ z)
    (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
      L.exhaustion.space_increasing (le_max_right _ _)⟩)
  obtain ⟨n, hjn, hcompare⟩ := blowupSequence_compact_metric_comparison
    P E t x ht hR L j K hK hstage 1 zero_lt_one
  refine ⟨2 * d, mul_pos (by norm_num) hd, ?_⟩
  filter_upwards [eventually_ge_atTop n] with k hk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G : RiemannianMetric 3 V :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  let f (z : L.limit.sliceCarrier.carrier) := ((L.embedding k).forward 0 hzero z).val
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (interior K) :=
    ((sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
      ((L.embedding k).forward_smooth 0 hzero)).mono
        (interior_subset.trans (hstage.trans (L.exhaustion.space_increasing (hjn.trans hk))))
  have hbound (z : L.limit.sliceCarrier.carrier) (hz : z ∈ interior K)
      (v : TangentSpace (𝓡 3) z) :
      G.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ 2 * g.tangentNorm z v := by
    have hh := hcompare k hk z (interior_subset hz) v
    have hnonneg : 0 ≤ g.inner z v v := by
      by_cases hv : v = 0
      · simp only [hv, map_zero, le_refl]
      · exact (g.pos z v hv).le
    have hquad : G.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z v)
        (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ 4 * g.inner z v v := by
      change Q * (E.flow.metric (t (L.subsequence k))).inner (f z)
        (mfderiv (𝓡 3) (𝓡 3) f z v) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ _
      have hupper := (le_abs_self _).trans hh
      linarith only [hupper, hnonneg]
    have hn := tangentNorm_pullback_le_of_quadratic_le g G f z v zero_lt_one
      (by norm_num : (0 : ℝ) ≤ 4) (by simpa only [one_mul] using hquad)
    have hsqrt : Real.sqrt (4 : ℝ) = 2 := by norm_num
    simpa only [div_one, hsqrt] using hn
  have hmaps : MapsTo gamma (Icc (0 : ℝ) 1) (interior K) :=
    fun z hz => hinside (mem_image_of_mem gamma hz)
  have hlen := pathELength_comp_le_of_tangentNorm_le g G f isOpen_interior hf
    (by norm_num : (0 : ℝ) ≤ 2) hbound gamma 0 1 hsmooth hmaps
  have hbase : f L.limit.base = x (L.subsequence k) :=
    congrArg (fun p : (generalizedFlow E.flow.base.flow).point => p.2.val)
      (L.base_preserving k _)
  have hdist := M13.edist_le_pathELength G
    (x := x (L.subsequence k)) (y := f y)
    ((hf.of_le (by simp)).comp hsmooth hmaps)
    (by simpa only [Function.comp_apply, hstart] using hbase)
    (congrArg f hend) zero_le_one
  have hstrict := ENNReal.mul_lt_mul_right
    (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top hlength
  exact (le_trans hdist hlen).trans_lt
    (hstrict.trans_eq (ENNReal.ofReal_mul (by norm_num)).symm)

end PoincareConjecture.M35.OrdinaryRealization
