import PoincareConjecture.Proofs.M35.Thm12_28.TransportedBall
import PoincareConjecture.Proofs.M09.RiemannianProper










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35



theorem image_ball_subset_of_tangentNorm_bound
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N)
    (U : Set M) (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (x : M) (r C : ℝ) (hC : 0 < C) (hball : g.ball x r ⊆ U)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ C * g.tangentNorm z v) :
    f '' g.ball x r ⊆ h.ball (f x) (C * r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨gamma, hstart, hend, hsmooth, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      (show g.edist x y < ENNReal.ofReal r from hy) zero_lt_one
  have hmaps : MapsTo gamma (Icc (0 : ℝ) 1) U := by
    intro s hs
    apply hball
    have hprefix : g.edist x (gamma s) ≤ g.pathELength gamma 0 1 :=
      (Manifold.riemannianEDist_le_pathELength hsmooth.contMDiffOn hstart rfl hs.1).trans
        (Manifold.pathELength_mono le_rfl hs.2)
    exact hprefix.trans_lt hlength
  have himage : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ gamma) (Icc 0 1) :=
    (hf.of_le (by simp)).comp hsmooth.contMDiffOn hmaps
  have hdist : h.edist (f x) (f y) ≤ h.pathELength (f ∘ gamma) 0 1 :=
    Manifold.riemannianEDist_le_pathELength himage (congrArg f hstart)
      (congrArg f hend) zero_le_one
  have hpath := pathELength_comp_le_of_tangentNorm_le g h f hU hf hC.le
    hbound gamma 0 1 hsmooth.contMDiffOn hmaps
  have hstrict := ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top hlength
  exact ((hdist.trans hpath).trans_lt hstrict).trans_eq (ENNReal.ofReal_mul hC.le).symm

namespace OrdinaryRealization



theorem blowupSequence_image_ball_bounded
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (r : ℝ) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let G : RiemannianMetric 3 StandardCapSpace :=
        M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
      let phi : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      phi '' (L.limit.flow.metric 0).ball L.limit.base r ⊆
        G.ball (x (L.subsequence k)) (2 * r) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  let g := L.limit.flow.metric 0
  let K : Set L.limit.sliceCarrier.carrier := closure (g.ball L.limit.base r)
  have hcomplete : MetricComplete g := L.limit.complete 0 L.limit.zero_mem
  have hK : IsCompact K := Proofs.M09.isCompact_closure_metric_ball g hcomplete L.limit.base r
  obtain ⟨j, hj⟩ := hK.elim_directed_cover L.exhaustion.space L.exhaustion.space_open
    (fun z _ => by rw [L.exhaustion.space_covers]; exact mem_univ z)
    (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
      L.exhaustion.space_increasing (le_max_right _ _)⟩)
  obtain ⟨N, hjN, hcompare⟩ := blowupSequence_compact_metric_comparison
    P E t x ht hR L j K hK hj 1 zero_lt_one
  filter_upwards [eventually_ge_atTop N] with k hk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  let phi : L.limit.sliceCarrier.carrier → StandardCapSpace :=
    fun z => ((L.embedding k).forward 0 hzero z).val
  have hbase : phi L.limit.base = x (L.subsequence k) :=
    congrArg (fun p : (generalizedFlow E.flow.base.flow).point => p.2.val)
      (L.base_preserving k _)
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  have hsub : g.ball L.limit.base r ⊆ L.exhaustion.space k :=
    fun _ hz => L.exhaustion.space_increasing (hjN.trans hk) (hj (subset_closure hz))
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ phi (g.ball L.limit.base r) :=
    ((sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
      ((L.embedding k).forward_smooth 0 hzero)).mono hsub
  have hopen : IsOpen (g.ball L.limit.base r) := by
    let : EMetricSpace L.limit.carrier.carrier := g.toEMetricSpace
    change IsOpen {z | edist L.limit.base z < ENNReal.ofReal r}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hspeed (y : L.limit.sliceCarrier.carrier) (hy : y ∈ g.ball L.limit.base r)
      (v : TangentSpace (𝓡 3) y) :
      G.tangentNorm (phi y) (mfderiv (𝓡 3) (𝓡 3) phi y v) ≤ 2 * g.tangentNorm y v := by
    have h := (abs_le.mp (hcompare k hk y (subset_closure hy) v)).2
    have hv : 0 ≤ g.inner y v v := by
      by_cases hv : v = 0
      · simp only [hv, map_zero, le_refl]
      · exact (g.pos y v hv).le
    have hbound : 1 * G.inner (phi y) (mfderiv (𝓡 3) (𝓡 3) phi y v)
        (mfderiv (𝓡 3) (𝓡 3) phi y v) ≤ 4 * g.inner y v v := by
      change Q * (E.flow.metric (t (L.subsequence k))).inner (phi y)
        (mfderiv (𝓡 3) (𝓡 3) phi y v) (mfderiv (𝓡 3) (𝓡 3) phi y v) -
          g.inner y v v ≤ 1 * g.inner y v v at h
      change 1 * (Q * (E.flow.metric (t (L.subsequence k))).inner (phi y)
        (mfderiv (𝓡 3) (𝓡 3) phi y v) (mfderiv (𝓡 3) (𝓡 3) phi y v)) ≤ _
      linarith only [h, hv]
    have hspeed := tangentNorm_pullback_le_of_quadratic_le g G phi y v
      zero_lt_one (by norm_num : (0 : ℝ) ≤ 4) hbound
    norm_num at hspeed ⊢
    exact hspeed
  change phi '' g.ball L.limit.base r ⊆ G.ball (x (L.subsequence k)) (2 * r)
  rw [← hbase]
  exact image_ball_subset_of_tangentNorm_bound g G phi (g.ball L.limit.base r)
    hopen hf L.limit.base r 2 (by norm_num) Subset.rfl hspeed

end OrdinaryRealization
end PoincareConjecture.M35
