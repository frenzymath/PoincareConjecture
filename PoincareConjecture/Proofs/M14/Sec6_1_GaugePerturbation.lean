import PoincareConjecture.Proofs.M14.Sec6_1_SupportedGaugeFamily
import PoincareConjecture.Proofs.M08.SquareVariationConstruction

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))

theorem exists_supportedBackwardGauge_radius {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η) (hsupport : tsupport η ⊆ Ioo τ₁ τ₂)
    (hsrc : ∀ t ∈ tsupport η, p.curve t ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ tsupport η, ∀ v ∈ Ioo (-r) r,
      (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b := by
  let J := Ioo τ₁ τ₂ ∩ p.curve ⁻¹' U
  have hp := p.curve_regular.continuousOn
  have hJ : IsOpen J := hp.isOpen_inter_preimage isOpen_Ioo hU
  have hL : ContinuousOn (fun t => lift (p.curve t)) J :=
    hlift.continuousOn.comp (hp.mono inter_subset_left) (fun _ ht => ht.2)
  have hshift : ContinuousOn
      (fun z : ℝ × ℝ => (lift (p.curve z.1)).2.val + z.2 • η z.1) (J ×ˢ univ) :=
    ((continuous_subtype_val.comp_continuousOn hL.snd).comp continuousOn_fst
      (fun _ hz => hz.1)).add
        (continuousOn_snd.smul (hη.continuous.comp continuous_fst).continuousOn)
  let Ω := (J ×ˢ univ) ∩
    (fun z : ℝ × ℝ => (lift (p.curve z.1)).2.val + z.2 • η z.1) ⁻¹'
      (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))
  have hΩ : IsOpen Ω :=
    hshift.isOpen_inter_preimage (hJ.prod isOpen_univ) (G.gaugeCover.spatial b).isOpen
  have hK : IsCompact (tsupport η) := isCompact_Icc.of_isClosed_subset
    (isClosed_tsupport η) (hsupport.trans Ioo_subset_Icc_self)
  have hzero : tsupport η ×ˢ {(0 : ℝ)} ⊆ Ω := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    have hv0 : v = 0 := mem_singleton_iff.mp hv
    refine ⟨⟨⟨hsupport ht, hsrc t ht⟩, mem_univ v⟩, ?_⟩
    change (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b
    simpa only [hv0, zero_smul, add_zero] using (lift (p.curve t)).2.property
  obtain ⟨r, hr, _, hKr⟩ := M08.exists_squareTube_radius hK hΩ hzero zero_lt_one
  exact ⟨r, hr, fun t ht v hv => (hKr (show (t, v) ∈ tsupport η ×ˢ Ioo (-r) r
    from ⟨ht, hv⟩)).2⟩

noncomputable def pathOfSupportedGaugePerturbation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (ha : τ₁ < a) (hac : a < c) (hc : c < τ₂)
    (hη : ContDiff ℝ ∞ η) (hsupport : tsupport η ⊆ Ioo a c)
    (hsrc : ∀ t ∈ tsupport η, p.curve t ∈ U) (v : ℝ)
    (hshift : ∀ t ∈ tsupport η,
      (lift (p.curve t)).2.val + v • η t ∈ G.gaugeCover.spatial b) :
    M14BackwardPath G T τ₁ τ₂ x y := by
  have hsupp : tsupport η ⊆ Ioo τ₁ τ₂ :=
    fun _ ht => ⟨ha.trans (hsupport ht).1, (hsupport ht).2.trans hc⟩
  apply pathOfCompactPerturbation hM12 p (supportedBackwardGaugeFamily p b lift η v)
    ha hac hc
  · exact supportedBackwardGaugeFamily_continuousOn p b lift η hU hlift hright hη
      hsupp hsrc hshift
  · exact supportedBackwardGaugeFamily_contMDiffOn p b lift η hU hlift hright hη hsrc hshift
  · intro t ht
    apply supportedBackwardGaugeFamily_time p b lift η (fun s hs => ?_) ht v
    exact ((G.gaugeCover.cylinder b).time_eq (lift (p.curve s))).symm.trans
      (congrArg G.spacetime.timeFunction (hright _ (hsrc s hs)))
  · intro t ht
    exact supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η
      (fun hs => ht (Ioo_subset_Icc_self (hsupport hs))) v

theorem isLocalMin_middleAction_supportedBackwardGauge
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hmin : M14IsMinimizing p)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (ha : τ₁ < a) (hac : a < c) (hc : c < τ₂)
    (hη : ContDiff ℝ ∞ η) (hsupport : tsupport η ⊆ Ioo a c)
    (hsrc : ∀ t ∈ tsupport η, p.curve t ∈ U) :
    IsLocalMin (fun v => ∫ t in a..c,
      M14RawLIntegrand G (supportedBackwardGaugeFamily p b lift η v)
        (projectedCurveVelocity G (supportedBackwardGaugeFamily p b lift η v)) t) 0 := by
  have hsupp : tsupport η ⊆ Ioo τ₁ τ₂ :=
    fun _ ht => ⟨ha.trans (hsupport ht).1, (hsupport ht).2.trans hc⟩
  obtain ⟨r, hr, hshift⟩ := exists_supportedBackwardGauge_radius p b lift η hU hlift hη hsupp hsrc
  have hzero : supportedBackwardGaugeFamily p b lift η 0 = p.curve :=
    funext (supportedBackwardGaugeFamily_at_zero p b lift η (fun t ht => hright _ (hsrc t ht)))
  have hbase : (∫ t in a..c, M14RawLIntegrand G (supportedBackwardGaugeFamily p b lift η 0)
      (projectedCurveVelocity G (supportedBackwardGaugeFamily p b lift η 0)) t) =
        ∫ t in a..c, M14BackwardLIntegrand G p t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hac.le
    intro t ht
    exact rawLIntegrand_eq_backward_of_eventuallyEq p ⟨ha.trans ht.1, ht.2.trans hc⟩
      (Filter.EventuallyEq.of_eq hzero)
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with v hv
  rw [hbase]
  apply middleAction_le_compactPerturbation hM12 p hmin
    (supportedBackwardGaugeFamily p b lift η v) ha hac hc
  · exact supportedBackwardGaugeFamily_continuousOn p b lift η hU hlift hright hη hsupp hsrc
      (fun t ht => hshift t ht v hv)
  · exact supportedBackwardGaugeFamily_contMDiffOn p b lift η hU hlift hright hη hsrc
      (fun t ht => hshift t ht v hv)
  · intro t ht
    apply supportedBackwardGaugeFamily_time p b lift η (fun s hs => ?_) ht v
    exact ((G.gaugeCover.cylinder b).time_eq (lift (p.curve s))).symm.trans
      (congrArg G.spacetime.timeFunction (hright _ (hsrc s hs)))
  · intro t ht
    exact supportedBackwardGaugeFamily_eq_of_not_tsupport p b lift η
      (fun hs => ht (Ioo_subset_Icc_self (hsupport hs))) v

end PoincareConjecture.M14
