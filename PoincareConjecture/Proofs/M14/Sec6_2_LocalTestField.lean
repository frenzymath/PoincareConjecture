import PoincareConjecture.Proofs.M14.Sec6_2_LocalTestVariation
import PoincareConjecture.Proofs.M14.Sec6_2_VariationClock
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension










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




theorem gaugeShiftFamily_parameter_mfderiv (s : ℝ) :
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun v => gaugeShiftFamily R b lift η (s, v)) 0 (1 : ℝ) =
      ((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 (η s)).val := by
  let c := (lift (R.curve s)).2
  let t := (lift (R.curve s)).1
  let f := fun q : G.gaugeCover.spatial b => (G.gaugeCover.cylinder b).toSpacetime (t, q)
  have hf : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (spacetimeModel n) ∞ f :=
    (G.gaugeCover.cylinder b).smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hshift := (G.gaugeCover.spatial b).affineShift_parameter_contMDiffAt c (η s)
  have hd := mfderiv_comp_apply_of_eq (x := (0 : ℝ))
    (hf.mdifferentiable (by simp) c) (hshift.mdifferentiableAt (by simp))
    (show (G.gaugeCover.spatial b).affineShift c ((0 : ℝ) • η s) = c by
      rw [zero_smul, TopologicalSpace.Opens.affineShift_zero]) (1 : ℝ)
  rw [TopologicalSpace.Opens.affineShift_parameter_mfderiv] at hd
  simpa only [f, c, t, Function.comp_def, gaugeShiftFamily, zero_smul,
    TopologicalSpace.Opens.affineShift_zero,
    (G.gaugeCover.metric b).spatialTangentEquiv_eq] using hd




theorem supportedGaugeFamily_parameter_mfderiv
    (hright : ∀ s ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (R.curve s)) = R.curve s) (s : ℝ) :
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
      (fun v => supportedGaugeFamily R b lift η (s, v)) 0 (1 : ℝ) =
      ((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 (η s)).val := by
  by_cases hs : s ∈ tsupport η
  · have heq : (fun v => supportedGaugeFamily R b lift η (s, v)) =
        (fun v => gaugeShiftFamily R b lift η (s, v)) :=
      funext (fun _ => supportedGaugeFamily_eq_gauge R b lift η (hright s hs))
    rw [heq]
    exact gaugeShiftFamily_parameter_mfderiv R b lift η s
  · have heq : (fun v => supportedGaugeFamily R b lift η (s, v)) =
        (fun _ : ℝ => R.curve s) :=
      funext (fun _ => supportedGaugeFamily_eq_of_not_tsupport R b lift η hs)
    rw [heq, image_eq_zero_of_notMem_tsupport hs, map_zero]
    simp only [mfderiv_const, zero_apply, Submodule.coe_zero]

private theorem horizontal_transport_val {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : (h.symm ▸ v : G.Horizontal r).val = v.val := by
  cases h
  rfl



theorem variationField_supportedGauge_val (V : M14LVariationData G p R)
    (hV : ∀ s v, V.squareFamily s v = supportedGaugeFamily R b lift η (s, v))
    (hright : ∀ s ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (R.curve s)) = R.curve s)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    (M14VariationField V s).val =
      ((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 (η s)).val := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have htransport : (M14VariationField V s).val = (M14EndpointVariationField V s 0).val :=
    horizontal_transport_val (V.square_base s) _
  rw [htransport, endpointVariationField_val_eq_tangent V hs hzero]
  have heq : (fun v => V.squareFamily s v) =
      (fun v => supportedGaugeFamily R b lift η (s, v)) := funext (hV s)
  rw [heq]
  exact supportedGaugeFamily_parameter_mfderiv R b lift η hright s

omit b lift η in



theorem exists_supportedGaugeTest_at {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (W : G.Horizontal (R.curve s)) :
    ∃ b : G.gaugeCover.index, ∃ U : Set G.Point,
      ∃ lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b,
      IsOpen U ∧ ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U ∧
      (∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q) ∧
      ∃ η : ℝ → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ η ∧
        tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∧
        (∀ r ∈ tsupport η, R.curve r ∈ U) ∧
        ((G.gaugeCover.metric b).spatialTangentEquiv
          (lift (R.curve s)).1 (lift (R.curve s)).2 (η s)).val = W.val := by
  obtain ⟨b, U, lift, hU, hsU, hlift, hright, _⟩ := exists_smooth_gauge_lift G (R.curve s)
  let J := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∩ R.curve ⁻¹' U
  have hR : ContinuousOn R.curve (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :=
    R.smooth.continuousOn.mono (Ioo_subset_Icc_self.trans R.interval_subset)
  have hJ : IsOpen J := hR.isOpen_inter_preimage isOpen_Ioo hU
  obtain ⟨ζ, hζs, _, hζ, _, hζone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hJ.mem_nhds ⟨hs, hsU⟩)
  have hW : ∃ v : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (lift (R.curve s))),
      v.val = W.val := by
    rw [hright _ hsU]
    exact ⟨W, rfl⟩
  obtain ⟨v, hv⟩ := hW
  obtain ⟨w, hw⟩ := ((G.gaugeCover.metric b).spatialTangentEquiv
    (lift (R.curve s)).1 (lift (R.curve s)).2).surjective v
  refine ⟨b, U, lift, hU, hlift, hright, fun r => ζ r • w,
    hζ.smul contDiff_const, ?_, ?_, ?_⟩
  · intro r hr
    exact (hζs (tsupport_smul_subset_left ζ (fun _ => w) hr)).1
  · intro r hr
    exact (hζs (tsupport_smul_subset_left ζ (fun _ => w) hr)).2
  · have hvalue : (G.gaugeCover.metric b).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 (ζ s • w) = v := by
      rw [hζone, one_smul, hw]
    exact (congrArg Subtype.val hvalue).trans hv

end PoincareConjecture.M14
