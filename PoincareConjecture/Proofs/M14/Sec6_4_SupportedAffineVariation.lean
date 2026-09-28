import PoincareConjecture.Proofs.M14.Sec6_4_SupportedAffineFamily
import PoincareConjecture.Proofs.M14.Sec6_2_LocalTestVariation











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p} (V : M14LVariationData G p R) (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ)




theorem exists_supportedAffineGauge_radius {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U) :
    ∃ r : ℝ, 0 < r ∧ r ≤ V.radius ∧ ∀ s ∈ tsupport η, ∀ v ∈ Ioo (-r) r,
      V.squareFamily s v ∈ U ∧
        (lift (V.squareFamily s v)).2.val + (c * v) • η s ∈ G.gaugeCover.spatial b := by
  let α : ℝ × ℝ → G.Point := fun z => V.squareFamily z.1 z.2
  let A := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ×ˢ V.parameterDomain
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hA : IsOpen A := isOpen_Ioo.prod hP
  have hα : ContinuousOn α A := V.square_smooth.continuousOn.mono
    (fun _ hz => V.square_contains ⟨Ioo_subset_Icc_self hz.1, hz.2⟩)
  let J := A ∩ α ⁻¹' U
  have hJ : IsOpen J := hα.isOpen_inter_preimage hA hU
  have hL : ContinuousOn (lift ∘ α) J :=
    hlift.continuousOn.comp (hα.mono inter_subset_left) (fun _ hz => hz.2)
  let shift := fun z : ℝ × ℝ => (lift (α z)).2.val + (c * z.2) • η z.1
  have hshift : ContinuousOn shift J :=
    (continuous_subtype_val.comp_continuousOn hL.snd).add
      ((continuousOn_const.mul continuousOn_snd).smul
        (hη.continuous.comp continuous_fst).continuousOn)
  let Ω := J ∩ shift ⁻¹' (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))
  have hΩ : IsOpen Ω := hshift.isOpen_inter_preimage hJ (G.gaugeCover.spatial b).isOpen
  have hK : IsCompact (tsupport η) := isCompact_Icc.of_isClosed_subset
    (isClosed_tsupport η) (hsupport.trans Ioo_subset_Icc_self)
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hKzero : tsupport η ×ˢ {(0 : ℝ)} ⊆ Ω := by
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    have hv0 : v = 0 := mem_singleton_iff.mp hv
    subst v
    refine ⟨⟨⟨hsupport hs, hzero⟩, ?_⟩, ?_⟩
    · change V.squareFamily s 0 ∈ U
      rw [V.square_base]
      exact hsrc s hs
    · change (lift (V.squareFamily s 0)).2.val + (c * 0) • η s ∈ G.gaugeCover.spatial b
      simpa only [mul_zero, zero_smul, add_zero] using (lift (V.squareFamily s 0)).2.property
  obtain ⟨r, hr, hrv, hKr⟩ := M08.exists_squareTube_radius hK hΩ hKzero V.radius_pos
  refine ⟨r, hr, hrv, ?_⟩
  intro s hs v hv
  have h := hKr (show (s, v) ∈ tsupport η ×ˢ Ioo (-r) r from ⟨hs, hv⟩)
  exact ⟨h.1.2, h.2⟩




theorem exists_supportedAffineGauge_variation (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hfix : M14BothEndpointsFixed V) {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U) :
    ∃ W : M14LVariationData G p R, M14BothEndpointsFixed W ∧
      ∀ s v, W.squareFamily s v = supportedAffineGaugeFamily V b lift η c (s, v) := by
  obtain ⟨r, hr, hrv, hshift⟩ := exists_supportedAffineGauge_radius V b lift η c hU hlift hη
    hsupport hsrc
  have hparam : Ioo (-r) r ⊆ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact Ioo_subset_Ioo (neg_le_neg hrv) hrv
  have hH := supportedAffineGaugeFamily_contMDiffOn V b lift η c hU hlift hright hη
    hsupport hparam (fun s hs v hv => (hshift s hs v hv).1)
    (fun s hs v hv => (hshift s hs v hv).2)
  have hclock : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v ∈ Ioo (-r) r,
      G.spacetime.timeFunction (supportedAffineGaugeFamily V b lift η c (s, v)) = T - s ^ 2 :=
    fun s hs v hv => supportedAffineGaugeFamily_time V b lift η c hparam
      (fun t ht u hu => hright _ (hshift t ht u hu).1) hs hv
  have hzero := supportedAffineGaugeFamily_at_zero V b lift η c
    (fun s hs => hright _ (hsrc s hs))
  refine ⟨variationOfSquare hM12 R (supportedAffineGaugeFamily V b lift η c) r hr hH hclock hzero,
    ?_, fun _ _ => rfl⟩
  apply variationOfSquare_bothEndpointsFixed
  · intro v hv
    have hs : Real.sqrt τ₁ ∉ tsupport η := fun hs => lt_irrefl _ (hsupport hs).1
    rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hs,
      V.square_agrees _ ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩ v (hparam hv),
      Real.sq_sqrt p.tau_nonneg]
    exact V.left_endpoint_fixed_spec.mp hfix.1 v (hparam hv)
  · intro v hv
    have hs : Real.sqrt τ₂ ∉ tsupport η := fun hs => lt_irrefl _ (hsupport hs).2
    rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hs,
      V.square_agrees _ ⟨Real.sqrt_le_sqrt p.tau_lt.le, le_rfl⟩ v (hparam hv),
      Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le)]
    exact V.right_endpoint_fixed_spec.mp hfix.2 v (hparam hv)

end PoincareConjecture.M14
