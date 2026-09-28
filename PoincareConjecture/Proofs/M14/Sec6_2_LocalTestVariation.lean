import PoincareConjecture.Proofs.M14.Sec6_2_SupportedGaugeFamily
import PoincareConjecture.Proofs.M08.SquareVariationConstruction

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))

theorem exists_supportedGauge_radius {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ tsupport η, ∀ v ∈ Ioo (-r) r,
      (lift (R.curve s)).2.val + v • η s ∈ G.gaugeCover.spatial b := by
  let J := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∩ R.curve ⁻¹' U
  have hR : ContinuousOn R.curve (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :=
    R.smooth.continuousOn.mono (Ioo_subset_Icc_self.trans R.interval_subset)
  have hJ : IsOpen J := hR.isOpen_inter_preimage isOpen_Ioo hU
  have hL : ContinuousOn (fun s => lift (R.curve s)) J :=
    hlift.continuousOn.comp (hR.mono inter_subset_left) (fun _ hs => hs.2)
  have hshift : ContinuousOn
      (fun z : ℝ × ℝ => (lift (R.curve z.1)).2.val + z.2 • η z.1) (J ×ˢ univ) :=
    ((continuous_subtype_val.comp_continuousOn hL.snd).comp continuousOn_fst
      (fun _ hz => hz.1)).add
        (continuousOn_snd.smul (hη.continuous.comp continuous_fst).continuousOn)
  let Ω := (J ×ˢ univ) ∩
    (fun z : ℝ × ℝ => (lift (R.curve z.1)).2.val + z.2 • η z.1) ⁻¹'
      (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))
  have hΩ : IsOpen Ω :=
    hshift.isOpen_inter_preimage (hJ.prod isOpen_univ) (G.gaugeCover.spatial b).isOpen
  have hK : IsCompact (tsupport η) := isCompact_Icc.of_isClosed_subset
    (isClosed_tsupport η) (hsupport.trans Ioo_subset_Icc_self)
  have hzero : tsupport η ×ˢ {(0 : ℝ)} ⊆ Ω := by
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    have hv0 : v = 0 := mem_singleton_iff.mp hv
    refine ⟨⟨⟨hsupport hs, hsrc s hs⟩, mem_univ v⟩, ?_⟩
    change (lift (R.curve s)).2.val + v • η s ∈ G.gaugeCover.spatial b
    simpa only [hv0, zero_smul, add_zero] using (lift (R.curve s)).2.property
  obtain ⟨r, hr, _, hKr⟩ := M08.exists_squareTube_radius hK hΩ hzero zero_lt_one
  exact ⟨r, hr, fun s hs v hv => (hKr (show (s, v) ∈ tsupport η ×ˢ Ioo (-r) r
    from ⟨hs, hv⟩)).2⟩

theorem exists_supportedGauge_variation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U) :
    ∃ V : M14LVariationData G p R, M14BothEndpointsFixed V ∧
      ∀ s v, V.squareFamily s v = supportedGaugeFamily R b lift η (s, v) := by
  obtain ⟨r, hr, hshift⟩ := exists_supportedGauge_radius R b lift η hU hlift hη
    hsupport hsrc
  have hH := supportedGaugeFamily_contMDiffOn R b lift η hU hlift hright hη
    hsupport hsrc hshift
  have hclock : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v ∈ Ioo (-r) r,
      G.spacetime.timeFunction (supportedGaugeFamily R b lift η (s, v)) = T - s ^ 2 := by
    intro s hs v _
    apply supportedGaugeFamily_time R b lift η (fun t ht => ?_) hs
    exact ((G.gaugeCover.cylinder b).time_eq (lift (R.curve t))).symm.trans
      (congrArg G.spacetime.timeFunction (hright _ (hsrc t ht)))
  have hzero := supportedGaugeFamily_at_zero R b lift η (fun s hs => hright _ (hsrc s hs))
  refine ⟨variationOfSquare hM12 R (supportedGaugeFamily R b lift η) r hr hH hclock hzero,
    ?_, fun _ _ => rfl⟩
  apply variationOfSquare_bothEndpointsFixed
  · intro v _
    have hs : Real.sqrt τ₁ ∉ tsupport η := fun hs => (lt_irrefl _ (hsupport hs).1)
    rw [supportedGaugeFamily_eq_of_not_tsupport R b lift η hs,
      R.agrees _ ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩, Real.sq_sqrt p.tau_nonneg]
  · intro v _
    have hs : Real.sqrt τ₂ ∉ tsupport η := fun hs => (lt_irrefl _ (hsupport hs).2)
    rw [supportedGaugeFamily_eq_of_not_tsupport R b lift η hs,
      R.agrees _ ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩,
      Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le)]

end PoincareConjecture.M14
