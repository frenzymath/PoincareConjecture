import PoincareConjecture.Proofs.M32.Claim11_34.ZeroSlice
import PoincareConjecture.Proofs.M32.Claim11_34.Noncompact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.BilinearConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LimitTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

theorem blowup_tendstoUniformlyOn_zeroCoefficient
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 3) q).target) (a b : Fin 3) :
    TendstoUniformlyOn
      (fun k y => blowupPullbackCoefficient (G.embedding k) q a b (0, y))
      (fun y => FlowCarrier.coordinateCoefficient G.limit.carrier q
        (fun t x v w => (G.limit.flow.metric t).inner x v w) a b (0, y))
      atTop K := by
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G (hK.image_of_continuousOn hc)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hdom : ({0} ×ˢ K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) ⊆
      {p | p ∈ blowupMetricChartDomain G.limit q ∧
        (extChartAt (𝓡 3) q).symm p.2 ∈ G.exhaustion.space j} := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨G.limit.zero_mem, hKc hy⟩, hj (mem_image_of_mem _ hy)⟩
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j 0 ({0} ×ˢ K)
    (isCompact_singleton.prod hK) hdom ε hε
  filter_upwards [eventually_ge_atTop N] with k hk y hy
  have h := (hN k hk).2 a b (0, y) ⟨rfl, hy⟩
  rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero] at h
  exact (dist_comm _ _).trans_lt h

private noncomputable def zeroChartPullbackForm (G : GeneralizedBlowupConvergence S J)
    (q : G.limit.carrier.carrier) (k : ℕ) (y : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := by
  let c := extChartAt (𝓡 3) q
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (c.symm y)) := by
    unfold TangentSpace; infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (c.symm y)) := by
    unfold TangentSpace; infer_instance
  let A : EuclideanSpace ℝ (Fin 3) →L[ℝ] TangentSpace (𝓡 3) (c.symm y) :=
    mfderiv (𝓡 3) (𝓡 3) c.symm y
  exact ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 3) (c.symm y)) (F := TangentSpace (𝓡 3) (c.symm y)) (G := ℝ)
    (E' := EuclideanSpace ℝ (Fin 3)) (F' := EuclideanSpace ℝ (Fin 3))
    (blowup_zeroPullbackForm G k (c.symm y)) A A

private theorem zeroChartPullbackForm_basis (G : GeneralizedBlowupConvergence S J)
    (q : G.limit.carrier.carrier) (k : ℕ) (y : EuclideanSpace ℝ (Fin 3))
    (a b : Fin 3) :
    zeroChartPullbackForm G q k y (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      blowupPullbackCoefficient (G.embedding k) q a b (0, y) := by
  have hzero : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  simp only [blowupPullbackCoefficient, hzero, dif_pos]
  rfl

private theorem tendstoUniformlyOn_zeroChartPullbackForm
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn (zeroChartPullbackForm G q)
      ((G.limit.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm)
      atTop K := by
  apply Poincare.Analysis.Calculus.tendstoUniformlyOn_bilinear_of_basis_entries
  intro a b
  simp only [zeroChartPullbackForm_basis]
  exact blowup_tendstoUniformlyOn_zeroCoefficient G q hK hKc a b

private theorem eventually_zeroPullbackForm_error_on_chart
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 3) q).target) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x : G.limit.carrier.carrier,
      x ∈ (extChartAt (𝓡 3) q).source → extChartAt (𝓡 3) q x ∈ K →
      ∀ v w : TangentSpace (𝓡 3) x,
        (G.limit.flow.metric 0).inner x v v ≤ 1 →
        (G.limit.flow.metric 0).inner x w w ≤ 1 →
        |blowup_zeroPullbackForm G k x v w - (G.limit.flow.metric 0).inner x v w| < ε := by
  let c := extChartAt (𝓡 3) q
  let g := G.limit.flow.metric 0
  have hpos : ∀ y ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 →
      0 < g.pullbackCoefficients c.symm y v v := by
    intro y hy v hv
    apply g.pos
    intro hzero
    have hi := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (hKc hy)
    have h := congrArg (fun A => A v) hi
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
      ContinuousLinearMap.comp_apply] at h
    change mfderiv (𝓡 3) (𝓡 3) c (c.symm y)
      (mfderiv (𝓡 3) (𝓡 3) c.symm y v) = v at h
    erw [hzero, map_zero] at h
    exact hv h.symm
  have hbound := eventually_bilinear_error_lt_on_unit_sublevels hK
    ((g.contDiffOn_chartCoefficients q).continuousOn.mono hKc) hpos
    (tendstoUniformlyOn_zeroChartPullbackForm G q hK hKc) hε
  filter_upwards [hbound] with k hk x hx hxK v w hv hw
  let A := mfderiv (𝓡 3) (𝓡 3) c x
  have hi (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (A z) = z := by
    have h := congrArg (fun B => B z)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
      ContinuousLinearMap.comp_apply] at h
    exact h
  have hval (z z' : TangentSpace (𝓡 3) x) :
      g.pullbackCoefficients c.symm (c x) (A z) (A z') = g.inner x z z' := by
    change g.inner (c.symm (c x)) _ _ = _
    erw [hi z, hi z', c.left_inv hx]
  have h := hk (c x) hxK (A v) (A w) ((hval v v).symm ▸ hv)
    ((hval w w).symm ▸ hw)
  rw [hval v w] at h
  change |blowup_zeroPullbackForm G k (c.symm (c x))
    (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (A v))
    (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) (A w)) - g.inner x v w| < ε at h
  erw [hi v, hi w, c.left_inv hx] at h
  exact h

theorem blowup_eventually_zeroPullbackForm_error
    (G : GeneralizedBlowupConvergence S J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v w : TangentSpace (𝓡 3) x,
      (G.limit.flow.metric 0).inner x v v ≤ 1 →
      (G.limit.flow.metric 0).inner x w w ≤ 1 →
      |blowup_zeroPullbackForm G k x v w - (G.limit.flow.metric 0).inner x v w| < ε := by
  apply hK.induction_on
      (p := fun A => ∀ᶠ k in atTop, ∀ x ∈ A, ∀ v w : TangentSpace (𝓡 3) x,
        (G.limit.flow.metric 0).inner x v v ≤ 1 →
        (G.limit.flow.metric 0).inner x w w ≤ 1 →
        |blowup_zeroPullbackForm G k x v w - (G.limit.flow.metric 0).inner x v w| < ε)
  · exact Eventually.of_forall (by simp)
  · intro A B hAB hB
    exact hB.mono fun k hk x hx => hk x (hAB hx)
  · intro A B hA hB
    filter_upwards [hA, hB] with k hkA hkB x hx
    exact hx.elim (hkA x) (hkB x)
  · intro q _
    let c := extChartAt (𝓡 3) q
    obtain ⟨r, hr, hrc⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (mem_extChartAt_target q))
    let V := c.source ∩ c ⁻¹' Metric.ball (c q) r
    have hV : V ∈ 𝓝 q := inter_mem (extChartAt_source_mem_nhds q)
      ((continuousAt_extChartAt q).preimage_mem_nhds (Metric.ball_mem_nhds (c q) hr))
    refine ⟨V, mem_nhdsWithin_of_mem_nhds hV, ?_⟩
    filter_upwards [eventually_zeroPullbackForm_error_on_chart G q
      (isCompact_closedBall (c q) r) hrc hε] with k hk x hx
    exact hk x hx.1 (Metric.ball_subset_closedBall hx.2)

theorem blowup_eventually_zero_tangentNorm_bounds
    (G : GeneralizedBlowupConvergence S J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      (blowup_zeroSourceMetric G k).tangentNorm (blowup_zeroSliceEmbedding G k x)
        (mfderiv (𝓡 3) (𝓡 3) (blowup_zeroSliceEmbedding G k) x v) ≤
        C * (G.limit.flow.metric 0).tangentNorm x v ∧
      (G.limit.flow.metric 0).tangentNorm x v ≤
        C * (blowup_zeroSourceMetric G k).tangentNorm (blowup_zeroSliceEmbedding G k x)
          (mfderiv (𝓡 3) (𝓡 3) (blowup_zeroSliceEmbedding G k) x v) := by
  have hε : 0 < (C - 1) / C := div_pos (sub_pos.mpr hC) (zero_lt_one.trans hC)
  filter_upwards [blowup_eventually_zeroPullbackForm_error G hK hε] with k hk x hx v
  apply (G.limit.flow.metric 0).tangentNorm_pullback_bounds_of_unit_error
    (blowup_zeroSourceMetric G k) (blowup_zeroSliceEmbedding G k) hC
  intro w hw
  have hwu : (G.limit.flow.metric 0).inner x w w ≤ 1 := Real.sqrt_le_one.mp hw
  rw [← blowup_zeroPullbackForm_eq_sourceMetric]
  exact (hk x hx w w hwu hwu).le

end PoincareConjecture.M32
