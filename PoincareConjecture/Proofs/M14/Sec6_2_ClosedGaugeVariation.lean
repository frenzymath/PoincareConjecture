import PoincareConjecture.Proofs.M14.Sec6_2_ClosedGaugeFamily
import PoincareConjecture.Proofs.M14.Sec6_2_SquareVariationRestriction
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

theorem exists_supportedGauge_radius_closed {U : Set G.Point}
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η)
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, R.curve s ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η,
      ∀ v ∈ Ioo (-r) r,
        (lift (R.curve s)).2.val + v • η s ∈ G.gaugeCover.spatial b := by
  let K := M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η
  let F := fun z : ℝ × ℝ => (lift (R.curve z.1)).2.val + z.2 • η z.1
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_tsupport η)
  have hR : ContinuousOn R.curve K :=
    R.smooth.continuousOn.mono (inter_subset_left.trans R.interval_subset)
  have hL : ContinuousOn (fun s => lift (R.curve s)) K :=
    hlift.continuousOn.comp hR hsrc
  have hF : ContinuousOn F (K ×ˢ univ) :=
    ((continuous_subtype_val.comp_continuousOn hL.snd).comp continuousOn_fst
      (fun _ hz => hz.1)).add
        (continuousOn_snd.smul (hη.continuous.comp continuous_fst).continuousOn)
  obtain ⟨Ω, hΩ, heq⟩ := continuousOn_iff'.mp hF
    (G.gaugeCover.spatial b) (G.gaugeCover.spatial b).isOpen
  have hzero : K ×ˢ {(0 : ℝ)} ⊆ Ω := by
    rintro ⟨s, v⟩ ⟨hs, hv⟩
    have hv0 : v = 0 := mem_singleton_iff.mp hv
    have hz : (s, v) ∈ F ⁻¹' (G.gaugeCover.spatial b) ∩ (K ×ˢ univ) := by
      refine ⟨?_, hs, mem_univ v⟩
      change (lift (R.curve s)).2.val + v • η s ∈ G.gaugeCover.spatial b
      simpa only [hv0, zero_smul, add_zero] using (lift (R.curve s)).2.property
    rw [heq] at hz
    exact hz.1
  obtain ⟨r, hr, _, hKr⟩ := M08.exists_squareTube_radius hK hΩ hzero zero_lt_one
  refine ⟨r, hr, ?_⟩
  intro s hs v hv
  have hz : (s, v) ∈ Ω ∩ (K ×ˢ univ) := ⟨hKr ⟨hs, hv⟩, hs, mem_univ v⟩
  rw [← heq] at hz
  exact hz.1

theorem exists_supportedGauge_variation_closed (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, R.curve s ∈ U) :
    ∃ V : M14LVariationData G p R, ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      ∀ v, V.squareFamily s v = supportedGaugeFamily R b lift η (s, v) := by
  obtain ⟨r, hr, hshift⟩ := exists_supportedGauge_radius_closed R b lift η hlift hη hsrc
  have hH := supportedGaugeFamily_contMDiffOn_closed R b lift η hU hlift hright hη hsrc hshift
  have hzero (s : ℝ) (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
      supportedGaugeFamily R b lift η (s, 0) = R.curve s := by
    by_cases ht : s ∈ tsupport η
    · rw [supportedGaugeFamily_eq_gauge R b lift η (hright _ (hsrc s ⟨hs, ht⟩))]
      simp only [gaugeShiftFamily, zero_smul, TopologicalSpace.Opens.affineShift_zero,
        Prod.mk.eta, hright _ (hsrc s ⟨hs, ht⟩)]
    · exact supportedGaugeFamily_eq_of_not_tsupport R b lift η ht
  have hclock (s : ℝ) (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (v : ℝ)
      (_hv : v ∈ Ioo (-r) r) :
      G.spacetime.timeFunction (supportedGaugeFamily R b lift η (s, v)) = T - s ^ 2 := by
    by_cases ht : s ∈ tsupport η
    · rw [supportedGaugeFamily_eq_gauge R b lift η (hright _ (hsrc s ⟨hs, ht⟩))]
      simp only [gaugeShiftFamily, (G.gaugeCover.cylinder b).time_eq]
      exact ((G.gaugeCover.cylinder b).time_eq (lift (R.curve s))).symm.trans
        ((congrArg G.spacetime.timeFunction (hright _ (hsrc s ⟨hs, ht⟩))).trans
          (R.curve_time s hs))
    · rw [supportedGaugeFamily_eq_of_not_tsupport R b lift η ht, R.curve_time s hs]
  obtain ⟨V, _, hV⟩ := exists_variationOfSquare_eqOn hM12 R
    (supportedGaugeFamily R b lift η) hr hH hclock hzero
  exact ⟨V, hV⟩

end PoincareConjecture.M14
