import PoincareConjecture.Proofs.M14.Sec6_4_SupportedAffineVariation
import PoincareConjecture.Proofs.M14.Sec6_4_VariationGaugeDerivative
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_LocalTestField

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_transport_value {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : (h.symm ▸ v : G.Horizontal r).val = v.val := by
  cases h
  rfl

private theorem horizontal_value_of_heq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} {w : G.Horizontal r} (hv : HEq v w) : v.val = w.val := by
  cases h
  exact congrArg Subtype.val (eq_of_heq hv)

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem variationField_val_eq_parameter_tangent (V : M14LVariationData G p R)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    (M14VariationField V s).val =
      mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun u => V.squareFamily s u) 0 (1 : ℝ) := by
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  exact (horizontal_transport_value (V.square_base s) (M14EndpointVariationField V s 0)).trans
    (endpointVariationField_val_eq_tangent V hs hzero)

variable (V W : M14LVariationData G p R) (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ)

theorem variationField_supportedAffineGauge_val
    (hW : ∀ s v, W.squareFamily s v = supportedAffineGaugeFamily V b lift η c (s, v))
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    (M14VariationField W s).val = (fun v w : SpacetimeModelVector n => v + c • w)
      (M14VariationField V s).val ((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 (η s)).val := by
  dsimp only
  by_cases hsupp : s ∈ tsupport η
  · obtain ⟨r, hr, hrv, hshift⟩ := exists_supportedAffineGauge_radius V b lift η c hU hlift hη
      hsupport hsrc
    let P := Ioo (-r) r
    have hP : IsOpen P := isOpen_Ioo
    have hzero : (0 : ℝ) ∈ P := ⟨neg_lt_zero.mpr hr, hr⟩
    have hparam : P ⊆ V.parameterDomain := by
      rw [V.parameterDomain_eq]
      exact Ioo_subset_Ioo (neg_le_neg hrv) hrv
    let β := fun z : ℝ × ℝ => lift (V.squareFamily z.1 z.2)
    have hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
        (tsupport η ×ˢ P) :=
      hlift.comp (V.square_smooth.mono (fun z hz =>
        V.square_contains ⟨Ioo_subset_Icc_self (hsupport hz.1), hparam hz.2⟩))
        (fun z hz => (hshift z.1 hz.1 z.2 hz.2).1)
    have hrec (t : ℝ) (ht : t ∈ tsupport η) (u : ℝ) (hu : u ∈ P) :
        (G.gaugeCover.cylinder b).toSpacetime (β (t, u)) = V.squareFamily t u :=
      hright _ (hshift t ht u hu).1
    let β' := fun z : ℝ × ℝ => ((β z).1,
      (G.gaugeCover.spatial b).affineShift (β z).2 ((c * z.2) • η z.1))
    have hβsp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
        (fun z => (β z).2) (tsupport η ×ˢ P) := fun z hz => (hβ z hz).snd
    have hv : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun z : ℝ × ℝ => (c * z.2) • η z.1) :=
      (contMDiff_const.mul contMDiff_snd).smul (hη.contMDiff.comp contMDiff_fst)
    have hsp := (G.gaugeCover.spatial b).affineShift_contMDiffOn.comp
      (hβsp.prodMk hv.contMDiffOn) (fun z hz => (hshift z.1 hz.1 z.2 hz.2).2)
    have hβ' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β'
        (tsupport η ×ˢ P) := fun z hz => (hβ z hz).fst.prodMk (hsp z hz)
    have hrec' (t : ℝ) (ht : t ∈ tsupport η) (u : ℝ) (_hu : u ∈ P) :
        (G.gaugeCover.cylinder b).toSpacetime (β' (t, u)) = W.squareFamily t u := by
      rw [hW]
      simp only [supportedAffineGaugeFamily, if_pos ht]
      rfl
    have hβzero : β' (s, 0) = β (s, 0) := by
      simp only [β', mul_zero, zero_smul, TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta]
    have hslice := hβ.comp ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn
      (fun _ hu => ⟨hsupp, hu⟩)
    have hq := (gaugeLift_spatialCurve_contDiffOn b hslice).contDiffAt (hP.mem_nhds hzero)
    have hlin : HasDerivAt (fun u : ℝ => (c * u) • η s) (c • η s) 0 := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id (0 : ℝ)).const_mul c).smul_const (η s)
    have hderiv : deriv (fun u => (β' (s, u)).2.val) 0 =
        deriv (fun u => (β (s, u)).2.val) 0 + c • η s := by
      apply HasDerivAt.deriv
      apply ((hq.differentiableAt (by simp)).hasDerivAt.add hlin).congr_of_eventuallyEq
      filter_upwards [hP.mem_nhds hzero] with u hu
      exact (G.gaugeCover.spatial b).affineShift_val (hshift s hsupp u hu).2
    have hY := variationField_gauge V b hP hzero hβ hrec hsupp
    have hY' := variationField_gauge W b hP hzero hβ' hrec' hsupp
    rw [hderiv, hβzero] at hY'
    have hbase := (hrec s hsupp 0 hzero).trans (V.square_base s)
    have hβbase : β (s, 0) = lift (R.curve s) := congrArg lift (V.square_base s)
    rw [hβbase] at hbase hY hY'
    have hval := horizontal_value_of_heq hbase.symm hY
    have hval' := horizontal_value_of_heq hbase.symm hY'
    rw [hval', hval, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
  · have heq : (fun u => W.squareFamily s u) = fun u => V.squareFamily s u :=
      funext (fun u => (hW s u).trans
        (supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hsupp))
    rw [variationField_val_eq_parameter_tangent W hs, variationField_val_eq_parameter_tangent V hs,
      heq, image_eq_zero_of_notMem_tsupport hsupp, map_zero, Submodule.coe_zero,
      smul_zero, add_zero]
    rfl

theorem variationField_supportedAffineGauge_eq (Z : M14LVariationData G p R)
    (hW : ∀ s v, W.squareFamily s v = supportedAffineGaugeFamily V b lift η c (s, v))
    (hZ : ∀ s v, Z.squareFamily s v = supportedGaugeFamily R b lift η (s, v))
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    M14VariationField W s = M14VariationField V s + c • M14VariationField Z s := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul,
    variationField_supportedAffineGauge_val V W b lift η c hW hU hlift hright hη hsupport hsrc hs,
    variationField_supportedGauge_val R b lift η Z hZ (fun t ht => hright _ (hsrc t ht)) hs]

end PoincareConjecture.M14
