import PoincareConjecture.Proofs.M14.Sec6_4_ClosedAffineFamily
import PoincareConjecture.Proofs.M14.Sec6_2_SquareVariationRestriction
import PoincareConjecture.Proofs.M14.Mathlib.CompactFamilyTube

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

theorem exists_supportedAffineGauge_radius_closed {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiffOn ℝ ∞ η (M14SqrtParameterInterval τ₁ τ₂))
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, R.curve s ∈ U) :
    ∃ r : ℝ, 0 < r ∧ r ≤ V.radius ∧
      ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, ∀ v ∈ Ioo (-r) r,
        V.squareFamily s v ∈ U ∧
          (lift (V.squareFamily s v)).2.val + (c * v) • η s ∈ G.gaugeCover.spatial b := by
  let K := M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η
  let α : ℝ × ℝ → G.Point := fun z => V.squareFamily z.1 z.2
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_tsupport η)
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hα : ContinuousOn α (K ×ˢ V.parameterDomain) := V.square_smooth.continuousOn.mono
    (fun _ hz => V.square_contains ⟨hz.1.1, hz.2⟩)
  obtain ⟨N, hN, h0N, hNP, hNU⟩ := exists_open_parameter_tube hK hP hα hU hzero
    (fun s hs => by
      change V.squareFamily s 0 ∈ U
      rw [V.square_base]
      exact hsrc s hs)
  have hL : ContinuousOn (lift ∘ α) (K ×ˢ N) := hlift.continuousOn.comp
    (hα.mono (fun _ hz => ⟨hz.1, hNP hz.2⟩)) (fun _ hz => hNU _ hz.1 _ hz.2)
  let shift := fun z : ℝ × ℝ => (lift (α z)).2.val + (c * z.2) • η z.1
  have hshift : ContinuousOn shift (K ×ˢ N) :=
    (continuous_subtype_val.comp_continuousOn hL.snd).add
      ((continuousOn_const.mul continuousOn_snd).smul
        (hη.continuousOn.comp continuousOn_fst (fun _ hz => hz.1.1)))
  obtain ⟨O, hO, h0O, hON, hOS⟩ := exists_open_parameter_tube hK hN hshift
    (G.gaugeCover.spatial b).isOpen h0N (fun s _ => by
      change (lift (V.squareFamily s 0)).2.val + (c * 0) • η s ∈
        G.gaugeCover.spatial b
      simpa only [mul_zero, zero_smul, add_zero] using
        (lift (V.squareFamily s 0)).2.property)
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h0O)
  refine ⟨min ε V.radius, lt_min hε V.radius_pos, min_le_right _ _, ?_⟩
  intro s hs v hv
  have hvO : v ∈ O := hεO (by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left ε V.radius)) hv.1,
      hv.2.trans_le (min_le_left ε V.radius)⟩)
  exact ⟨hNU s hs v (hON hvO), hOS s hs v hvO⟩

theorem exists_supportedAffineGauge_variation_closed
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiffOn ℝ ∞ η (M14SqrtParameterInterval τ₁ τ₂))
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, R.curve s ∈ U) :
    ∃ W : M14LVariationData G p R, W.parameterDomain ⊆ V.parameterDomain ∧
      ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v,
        W.squareFamily s v = supportedAffineGaugeFamily V b lift η c (s, v) := by
  obtain ⟨r, hr, hrv, hshift⟩ := exists_supportedAffineGauge_radius_closed V b lift η c
    hU hlift hη hsrc
  have hparam : Ioo (-r) r ⊆ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact Ioo_subset_Ioo (neg_le_neg hrv) hrv
  have hH := supportedAffineGaugeFamily_contMDiffOn_closed V b lift η c hU hlift hright hη
    hparam (fun s hs v hv => (hshift s hs v hv).1) (fun s hs v hv => (hshift s hs v hv).2)
  have hclock : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ v ∈ Ioo (-r) r,
      G.spacetime.timeFunction (supportedAffineGaugeFamily V b lift η c (s, v)) = T - s ^ 2 :=
    fun s hs v hv => supportedAffineGaugeFamily_time_closed V b lift η c hparam
      (fun t ht u hu => hright _ (hshift t ht u hu).1) hs hv
  have hzero : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      supportedAffineGaugeFamily V b lift η c (s, 0) = R.curve s :=
    fun s hs => supportedAffineGaugeFamily_zero_closed V b lift η c
      (fun t ht => hright _ (hsrc t ht)) hs
  obtain ⟨W, hWparam, hW⟩ := exists_variationOfSquare_eqOn hM12 R
    (supportedAffineGaugeFamily V b lift η c) hr hH hclock hzero
  exact ⟨W, hWparam ▸ hparam, hW⟩

end PoincareConjecture.M14
