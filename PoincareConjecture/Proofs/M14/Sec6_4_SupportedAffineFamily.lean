import PoincareConjecture.Proofs.M14.Sec6_2_SupportedGaugeFamily
import PoincareConjecture.Proofs.M14.Sec6_2_VariationClock

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p} (V : M14LVariationData G p R) (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n)) (c : ℝ)

noncomputable def affineGaugeFamily (z : ℝ × ℝ) : G.Point :=
  (G.gaugeCover.cylinder b).toSpacetime ((lift (V.squareFamily z.1 z.2)).1,
    (G.gaugeCover.spatial b).affineShift (lift (V.squareFamily z.1 z.2)).2
      ((c * z.2) • η z.1))

noncomputable def supportedAffineGaugeFamily (z : ℝ × ℝ) : G.Point := by
  classical
  exact if z.1 ∈ tsupport η then affineGaugeFamily V b lift η c z else V.squareFamily z.1 z.2

theorem supportedAffineGaugeFamily_eq_of_not_tsupport {z : ℝ × ℝ}
    (hz : z.1 ∉ tsupport η) :
    supportedAffineGaugeFamily V b lift η c z = V.squareFamily z.1 z.2 := by
  simp only [supportedAffineGaugeFamily, if_neg hz]

theorem supportedAffineGaugeFamily_eq_gauge {z : ℝ × ℝ}
    (hz : (G.gaugeCover.cylinder b).toSpacetime (lift (V.squareFamily z.1 z.2)) =
      V.squareFamily z.1 z.2) :
    supportedAffineGaugeFamily V b lift η c z = affineGaugeFamily V b lift η c z := by
  by_cases hs : z.1 ∈ tsupport η
  · simp only [supportedAffineGaugeFamily, if_pos hs]
  · rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hs]
    simp only [affineGaugeFamily, image_eq_zero_of_notMem_tsupport hs, smul_zero,
      TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta]
    exact hz.symm

theorem supportedAffineGaugeFamily_at_zero
    (hsrc : ∀ s ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (R.curve s)) = R.curve s) (s : ℝ) :
    supportedAffineGaugeFamily V b lift η c (s, 0) = R.curve s := by
  by_cases hs : s ∈ tsupport η
  · have hrec : (G.gaugeCover.cylinder b).toSpacetime (lift (V.squareFamily s 0)) =
        V.squareFamily s 0 := by rw [V.square_base]; exact hsrc s hs
    rw [supportedAffineGaugeFamily_eq_gauge V b lift η c hrec]
    simp only [affineGaugeFamily, mul_zero, zero_smul, TopologicalSpace.Opens.affineShift_zero,
      Prod.mk.eta, V.square_base, hsrc s hs]
  · rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hs, V.square_base]

private theorem squareFamily_interior_contMDiffAt {z : ℝ × ℝ}
    (hs : z.1 ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (hu : z.2 ∈ V.parameterDomain) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun w : ℝ × ℝ => V.squareFamily w.1 w.2) z := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hV := V.square_smooth.mono
    (show Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ×ˢ V.parameterDomain ⊆ V.squareDomain from
      fun _ hw => V.square_contains ⟨Ioo_subset_Icc_self hw.1, hw.2⟩)
  exact hV.contMDiffAt ((isOpen_Ioo.prod hP).mem_nhds ⟨hs, hu⟩)

theorem affineGaugeFamily_contMDiffAt {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η) {z : ℝ × ℝ}
    (hs : z.1 ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (hu : z.2 ∈ V.parameterDomain)
    (hz : V.squareFamily z.1 z.2 ∈ U)
    (hshift : (lift (V.squareFamily z.1 z.2)).2.val + (c * z.2) • η z.1 ∈
      G.gaugeCover.spatial b) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (affineGaugeFamily V b lift η c) z := by
  have hV := squareFamily_interior_contMDiffAt V hs hu
  have hL := ((hlift _ hz).contMDiffAt (hU.mem_nhds hz)).comp z hV
  have hv : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun w : ℝ × ℝ => (c * w.2) • η w.1) z :=
    (contMDiffAt_const.mul contMDiffAt_snd).smul
      (hη.contMDiff.contMDiffAt.comp z contMDiffAt_fst)
  have hS := (((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hshift).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hshift)).comp z
      (hL.snd.prodMk hv)
  exact (G.gaugeCover.cylinder b).smooth.contMDiffAt.comp z (hL.fst.prodMk hS)

theorem supportedAffineGaugeFamily_contMDiffOn {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    {P : Set ℝ} (hP : P ⊆ V.parameterDomain)
    (hsrc : ∀ s ∈ tsupport η, ∀ v ∈ P, V.squareFamily s v ∈ U)
    (hshift : ∀ s ∈ tsupport η, ∀ v ∈ P,
      (lift (V.squareFamily s v)).2.val + (c * v) • η s ∈ G.gaugeCover.spatial b) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (supportedAffineGaugeFamily V b lift η c) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) := by
  have hbase := V.square_smooth.mono
    (show M14SqrtParameterInterval τ₁ τ₂ ×ˢ P ⊆ V.squareDomain from
      fun _ hz => V.square_contains ⟨hz.1, hP hz.2⟩)
  intro z hz
  by_cases hsupportz : z.1 ∈ tsupport η
  · have hs := hsupport hsupportz
    have hV := squareFamily_interior_contMDiffAt V hs (hP hz.2)
    have heq : supportedAffineGaugeFamily V b lift η c =ᶠ[𝓝 z]
        affineGaugeFamily V b lift η c := by
      filter_upwards [hV.continuousAt.preimage_mem_nhds (hU.mem_nhds
        (hsrc _ hsupportz _ hz.2))] with w hw
      exact supportedAffineGaugeFamily_eq_gauge V b lift η c (hright _ hw)
    have hlocal := affineGaugeFamily_contMDiffAt V b lift η c hU hlift hη hs (hP hz.2)
      (hsrc _ hsupportz _ hz.2) (hshift _ hsupportz _ hz.2)
    exact (hlocal.congr_of_eventuallyEq heq).contMDiffWithinAt
  · have heq : supportedAffineGaugeFamily V b lift η c =ᶠ[𝓝 z]
        fun w => V.squareFamily w.1 w.2 := by
      filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage continuous_fst).mem_nhds
        hsupportz] with w hw
      exact supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hw
    exact (hbase z hz).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

theorem supportedAffineGaugeFamily_time {P : Set ℝ} (hP : P ⊆ V.parameterDomain)
    (hrec : ∀ s ∈ tsupport η, ∀ v ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (lift (V.squareFamily s v)) = V.squareFamily s v)
    {s v : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (hv : v ∈ P) :
    G.spacetime.timeFunction (supportedAffineGaugeFamily V b lift η c (s, v)) = T - s ^ 2 := by
  by_cases hsupport : s ∈ tsupport η
  · rw [supportedAffineGaugeFamily_eq_gauge V b lift η c (hrec s hsupport v hv)]
    have hclock := ((G.gaugeCover.cylinder b).time_eq (lift (V.squareFamily s v))).symm.trans
      (congrArg G.spacetime.timeFunction (hrec s hsupport v hv))
    simp only [affineGaugeFamily, (G.gaugeCover.cylinder b).time_eq, hclock,
      variation_squareFamily_time V hs (hP hv)]
  · rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hsupport,
      variation_squareFamily_time V hs (hP hv)]

end PoincareConjecture.M14
