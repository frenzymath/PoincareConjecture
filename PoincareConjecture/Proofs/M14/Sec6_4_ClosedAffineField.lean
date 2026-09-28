import PoincareConjecture.Proofs.M14.Sec6_4_ClosedAffineVariation
import PoincareConjecture.Proofs.M14.Sec6_4_SupportedAffineField










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_value_of_heq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} {w : G.Horizontal r} (hv : HEq v w) : v.val = w.val := by
  cases h
  exact congrArg Subtype.val (eq_of_heq hv)

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p} (V W : M14LVariationData G p R) (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ)




theorem variationField_supportedAffineGauge_val_closed
    (hW : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v,
      W.squareFamily s v = supportedAffineGaugeFamily V b lift η c (s, v))
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiffOn ℝ ∞ η (M14SqrtParameterInterval τ₁ τ₂))
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, R.curve s ∈ U)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    (M14VariationField W s).val = (fun v w : SpacetimeModelVector n => v + c • w)
      (M14VariationField V s).val ((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (R.curve s)).1 (lift (R.curve s)).2 (η s)).val := by
  dsimp only
  by_cases hsupp : s ∈ tsupport η
  · obtain ⟨r, hr, hrv, hshift⟩ := exists_supportedAffineGauge_radius_closed V b lift η c
      hU hlift hη hsrc
    let K := M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η
    let P := Ioo (-r) r
    have hsK : s ∈ K := ⟨hs, hsupp⟩
    have hP : IsOpen P := isOpen_Ioo
    have hzero : (0 : ℝ) ∈ P := ⟨neg_lt_zero.mpr hr, hr⟩
    have hparam : P ⊆ V.parameterDomain := by
      rw [V.parameterDomain_eq]
      exact Ioo_subset_Ioo (neg_le_neg hrv) hrv
    let β := fun z : ℝ × ℝ => lift (V.squareFamily z.1 z.2)
    have hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β (K ×ˢ P) :=
      hlift.comp (V.square_smooth.mono (fun z hz =>
        V.square_contains ⟨hz.1.1, hparam hz.2⟩))
        (fun z hz => (hshift z.1 hz.1 z.2 hz.2).1)
    have hrec (t : ℝ) (ht : t ∈ K) (u : ℝ) (hu : u ∈ P) :
        (G.gaugeCover.cylinder b).toSpacetime (β (t, u)) = V.squareFamily t u :=
      hright _ (hshift t ht u hu).1
    let β' := fun z : ℝ × ℝ => ((β z).1,
      (G.gaugeCover.spatial b).affineShift (β z).2 ((c * z.2) • η z.1))
    have hβsp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
        (fun z => (β z).2) (K ×ˢ P) := fun z hz => (hβ z hz).snd
    have hη' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun z : ℝ × ℝ => η z.1) (K ×ˢ P) :=
      hη.contMDiffOn.comp contMDiffOn_fst (fun _ hz => hz.1.1)
    have hv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : ℝ × ℝ => (c * z.2) • η z.1) (K ×ˢ P) :=
      (contMDiffOn_const.mul contMDiffOn_snd).smul hη'
    have hsp := (G.gaugeCover.spatial b).affineShift_contMDiffOn.comp
      (hβsp.prodMk hv) (fun z hz => (hshift z.1 hz.1 z.2 hz.2).2)
    have hβ' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β'
        (K ×ˢ P) := fun z hz => (hβ z hz).fst.prodMk (hsp z hz)
    have hrec' (t : ℝ) (ht : t ∈ K) (u : ℝ) (_hu : u ∈ P) :
        (G.gaugeCover.cylinder b).toSpacetime (β' (t, u)) = W.squareFamily t u := by
      rw [hW t ht.1]
      simp only [supportedAffineGaugeFamily, if_pos ht.2]
      rfl
    have hβzero : β' (s, 0) = β (s, 0) := by
      simp only [β', mul_zero, zero_smul, TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta]
    have hslice := hβ.comp ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn
      (fun _ hu => ⟨hsK, hu⟩)
    have hq := (gaugeLift_spatialCurve_contDiffOn b hslice).contDiffAt (hP.mem_nhds hzero)
    have hlin : HasDerivAt (fun u : ℝ => (c * u) • η s) (c • η s) 0 := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id (0 : ℝ)).const_mul c).smul_const (η s)
    have hderiv : deriv (fun u => (β' (s, u)).2.val) 0 =
        deriv (fun u => (β (s, u)).2.val) 0 + c • η s := by
      apply HasDerivAt.deriv
      apply ((hq.differentiableAt (by simp)).hasDerivAt.add hlin).congr_of_eventuallyEq
      filter_upwards [hP.mem_nhds hzero] with u hu
      exact (G.gaugeCover.spatial b).affineShift_val (hshift s hsK u hu).2
    have hY := variationField_gauge V b hP hzero hβ hrec hsK
    have hY' := variationField_gauge W b hP hzero hβ' hrec' hsK
    rw [hderiv, hβzero] at hY'
    have hbase := (hrec s hsK 0 hzero).trans (V.square_base s)
    have hβbase : β (s, 0) = lift (R.curve s) := congrArg lift (V.square_base s)
    rw [hβbase] at hbase hY hY'
    have hval := horizontal_value_of_heq hbase.symm hY
    have hval' := horizontal_value_of_heq hbase.symm hY'
    rw [hval', hval, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul]
  · have heq : (fun u => W.squareFamily s u) = fun u => V.squareFamily s u :=
      funext (fun u => (hW s hs u).trans
        (supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hsupp))
    rw [variationField_val_eq_parameter_tangent W hs, variationField_val_eq_parameter_tangent V hs,
      heq, image_eq_zero_of_notMem_tsupport hsupp, map_zero, Submodule.coe_zero,
      smul_zero, add_zero]
    rfl

omit W in



theorem supportedAffineGaugeFamily_fixed_of_zero {s : ℝ}
    (hηzero : η s = 0) (hfix : ∀ v, V.squareFamily s v = R.curve s)
    (hrec : s ∈ tsupport η →
      (G.gaugeCover.cylinder b).toSpacetime (lift (R.curve s)) = R.curve s) (v : ℝ) :
    supportedAffineGaugeFamily V b lift η c (s, v) = R.curve s := by
  by_cases ht : s ∈ tsupport η
  · simp only [supportedAffineGaugeFamily, if_pos ht, affineGaugeFamily, hfix, hηzero,
      smul_zero, TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta, hrec ht]
  · rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c ht, hfix]

end PoincareConjecture.M14
