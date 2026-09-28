import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedSpatialJets
import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.Topology.Instances.ENNReal.Lemmas













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 600000 in




theorem tendsto_backward_scalar_spatial_jets
    (hSlice : SpatialSliceJetConvergenceService.{0, 0, 0, 0, 0})
    {n : ℕ} {s' s : ℝ} {T0 : ℝ≥0∞} {J : ℕ → Set ℝ}
    (hzero : s' < 0 ∧ 0 < s)
    {S : PointedFlowSequence n s' s}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k, RicciFlow n (S.carrier k).carrier (J k))
    (htime : ∀ A : ℝ, 0 < A → ENNReal.ofReal A < T0 →
      ∀ᶠ k in atTop, Icc (-A) 0 ⊆ J k)
    (F : RicciFlow n G.limitCarrier.carrier (blowupBackwardInterval T0)) :
    let f := fun (q : G.limitCarrier.carrier) k
        (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
      ((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
          (extChartAt (𝓡 n) q).symm) z.2
    let g := fun (q : G.limitCarrier.carrier)
        (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
      (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2
    (∀ (q : G.limitCarrier.carrier) (m : ℕ)
        (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ blowupBackwardInterval T0 ×ˢ
        (extChartAt (𝓡 n) q).target →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f q k)
          (blowupBackwardInterval T0 ×ˢ (extChartAt (𝓡 n) q).target))
        (iteratedFDerivWithin ℝ m (g q)
          (blowupBackwardInterval T0 ×ˢ (extChartAt (𝓡 n) q).target)) atTop K) →
    ∀ (q : G.limitCarrier.carrier) (p : EuclideanSpace ℝ (Fin n)),
      p ∈ (extChartAt (𝓡 n) q).target →
      ∀ t ∈ blowupBackwardInterval T0, ∀ (r : ℕ) (a b : Fin n),
        Tendsto (fun k => iteratedFDeriv ℝ r
          (fun y => f q k (t, y)
            (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) p) atTop
          (𝓝 (iteratedFDeriv ℝ r
            (fun y => g q (t, y)
              (EuclideanSpace.basisFun (Fin n) ℝ a)
              (EuclideanSpace.basisFun (Fin n) ℝ b)) p)) := by
  classical
  intro f g hjets q p hp t ht r a b
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let B := E →L[ℝ] E →L[ℝ] ℝ
  let c := extChartAt (𝓡 n) q
  obtain ⟨δ, hδ, hδH⟩ := Metric.isOpen_iff.mp
    (isOpen_Iio.preimage ENNReal.continuous_ofReal) (-t) ht.2
  let A := -t + δ / 2
  have hAt : -t < A := by dsimp only [A]; linarith
  have hA : 0 < A := (neg_nonneg.mpr ht.1).trans_lt hAt
  have hAh : ENNReal.ofReal A < T0 := by
    apply hδH
    change dist A (-t) < δ
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hAt.le)]
    dsimp only [A]
    linarith
  have hsmall : Ioc (-A) (0 : ℝ) ⊆ blowupBackwardInterval T0 := by
    intro u hu
    exact ⟨hu.2, (ENNReal.ofReal_le_ofReal (show -u ≤ A by linarith [hu.1])).trans_lt hAh⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := 𝓡 n) q) p hp
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  let U := Metric.ball p ρ
  let Kbar := Metric.closedBall p ρ
  have hU : IsOpen U := Metric.isOpen_ball
  have hKbar : IsCompact Kbar := isCompact_closedBall p ρ
  have hKc : Kbar ⊆ c.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  have hUc : U ⊆ c.target := Metric.ball_subset_closedBall.trans hKc
  have hpU : p ∈ U := Metric.mem_ball_self hρ
  have hchart {y : E} (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  obtain ⟨N, hN⟩ := G.exists_exhaustion_superset
    (hKbar.image_of_continuousOn
      ((contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc))
  let ψ (k : ℕ) : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y => ((G.embedding k).toFun (0, y)).2
  have hmaps : ∀ᶠ k : ℕ in atTop,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (ψ k ∘ c.symm) U := by
    filter_upwards [eventually_ge_atTop N] with k hk y hy
    have hx : c.symm y ∈ G.exhaustion k := G.exhaustion_monotone hk
      (hN (mem_image_of_mem c.symm (Metric.ball_subset_closedBall hy)))
    exact (((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k)
      hzero hx).comp y (hchart (hUc hy))).contMDiffWithinAt
  let D := blowupBackwardInterval T0 ×ˢ c.target
  let Dloc := Ioc (-A) (0 : ℝ) ×ˢ U
  have hsource : ∀ᶠ k : ℕ in atTop, ContDiffOn ℝ ∞ (f q k) Dloc := by
    filter_upwards [hmaps,
      G.subsequence_strictMono.tendsto_atTop.eventually (htime A hA hAh)] with k hk htimek
    exact ((Fsrc (G.subsequence k)).contDiffOn_pullbackCoefficients_within hU hk).mono
      (prod_mono (fun u hu => htimek ⟨hu.1.le, hu.2⟩) (Subset.refl _))
  have htarget : ContDiffOn ℝ ∞ (g q) Dloc :=
    (F.contDiffOn_pullbackCoefficients_within hU
      ((contMDiffOn_extChartAt_symm (n := ∞) q).mono hUc)).mono
        (prod_mono hsmall (Subset.refl _))
  have hinter : D ∩ (Ioi (-A) ×ˢ U) = Dloc := by
    apply Subset.antisymm
    · intro z hz
      exact ⟨⟨hz.2.1, hz.1.1.1⟩, hz.2.2⟩
    · intro z hz
      exact ⟨⟨hsmall hz.1, hUc hz.2⟩, ⟨hz.1.1, hz.2⟩⟩
  have hrestrict (v : ℝ × E → B) {z : ℝ × E} (hz : z ∈ Dloc) :
      iteratedFDerivWithin ℝ r v Dloc z = iteratedFDerivWithin ℝ r v D z := by
    rw [← hinter]
    exact iteratedFDerivWithin_inter_open (isOpen_Ioi.prod hU) ⟨hz.1.1, hz.2⟩
  have hsingle : ({(t, p)} : Set (ℝ × E)) ⊆ Dloc :=
    singleton_subset_iff.mpr ⟨⟨by linarith, ht.1⟩, hpU⟩
  have hlocal : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ r (f q k) Dloc)
      (iteratedFDerivWithin ℝ r (g q) Dloc) atTop ({(t, p)} : Set (ℝ × E)) := by
    refine ((hjets q r {(t, p)} isCompact_singleton
      (singleton_subset_iff.mpr ⟨ht, hp⟩)).congr ?_).congr_right ?_
    · exact Eventually.of_forall fun k z hz => (hrestrict (f q k) (hsingle hz)).symm
    · intro z hz
      exact (hrestrict (g q) (hsingle hz)).symm
  have hr : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hspatial := hSlice hlocal (uniqueDiffOn_Ioc (-A) 0)
    hU hsingle hsource htarget hr
  let L : B →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ b)).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin n) ℝ a))
  let Lr := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin r => E) B ℝ L
  have heval := (Lr.uniformContinuous.comp_tendstoUniformlyOn hspatial).tendsto_at
    (mem_singleton (t, p))
  have hlimit : ContDiffAt ℝ ∞ (fun y => g q (t, y)) p :=
    (F.metric t).contDiffAt_pullbackCoefficients (hchart hp)
  change Tendsto (fun k => iteratedFDeriv ℝ r (L ∘ fun y => f q k (t, y)) p)
    atTop (𝓝 (iteratedFDeriv ℝ r (L ∘ fun y => g q (t, y)) p))
  rw [L.iteratedFDeriv_comp_left hlimit hr]
  refine heval.congr' ?_
  filter_upwards [hmaps] with k hk
  exact (L.iteratedFDeriv_comp_left
    (((Fsrc (G.subsequence k)).metric t).contDiffAt_pullbackCoefficients
      (hk.contMDiffAt (hU.mem_nhds hpU))) hr).symm

end PoincareConjecture.M30
