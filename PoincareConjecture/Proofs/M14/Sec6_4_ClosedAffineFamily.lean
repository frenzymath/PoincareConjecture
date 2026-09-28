import PoincareConjecture.Proofs.M14.Sec6_4_SupportedAffineFamily

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

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

theorem affineGaugeFamily_contMDiffWithinAt {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiffOn ℝ ∞ η (M14SqrtParameterInterval τ₁ τ₂))
    {P : Set ℝ} (hP : P ⊆ V.parameterDomain) {z : ℝ × ℝ}
    (hz : z ∈ M14SqrtParameterInterval τ₁ τ₂ ×ˢ P)
    (hsrc : V.squareFamily z.1 z.2 ∈ U)
    (hshift : (lift (V.squareFamily z.1 z.2)).2.val + (c * z.2) • η z.1 ∈
      G.gaugeCover.spatial b) :
    ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (affineGaugeFamily V b lift η c) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) z := by
  have hV := (V.square_smooth.mono
    (fun _ hw => V.square_contains ⟨hw.1, hP hw.2⟩)) z hz
  have hL := ((hlift _ hsrc).contMDiffAt (hU.mem_nhds hsrc)).comp_contMDiffWithinAt z hV
  have hη' : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun w : ℝ × ℝ => η w.1)
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) z :=
    (hη z.1 hz.1).contMDiffWithinAt.comp z contMDiffWithinAt_fst
      (fun w (hw : w ∈ M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) => hw.1)
  have hv : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun w : ℝ × ℝ => (c * w.2) • η w.1)
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) z :=
    (contMDiffWithinAt_const.mul contMDiffWithinAt_snd).smul hη'
  have hS := (((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hshift).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hshift)).comp_contMDiffWithinAt
      z (hL.snd.prodMk hv)
  exact (G.gaugeCover.cylinder b).smooth.contMDiffAt.comp_contMDiffWithinAt z
    (hL.fst.prodMk hS)

theorem supportedAffineGaugeFamily_contMDiffOn_closed {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiffOn ℝ ∞ η (M14SqrtParameterInterval τ₁ τ₂))
    {P : Set ℝ} (hP : P ⊆ V.parameterDomain)
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, ∀ v ∈ P,
      V.squareFamily s v ∈ U)
    (hshift : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, ∀ v ∈ P,
      (lift (V.squareFamily s v)).2.val + (c * v) • η s ∈ G.gaugeCover.spatial b) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (supportedAffineGaugeFamily V b lift η c) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) := by
  have hbase := V.square_smooth.mono
    (show M14SqrtParameterInterval τ₁ τ₂ ×ˢ P ⊆ V.squareDomain from
      fun _ hz => V.square_contains ⟨hz.1, hP hz.2⟩)
  intro z hz
  by_cases hs : z.1 ∈ tsupport η
  · have hmem := hsrc z.1 ⟨hz.1, hs⟩ z.2 hz.2
    have heq : supportedAffineGaugeFamily V b lift η c
        =ᶠ[𝓝[M14SqrtParameterInterval τ₁ τ₂ ×ˢ P] z] affineGaugeFamily V b lift η c := by
      filter_upwards [(hbase z hz).continuousWithinAt.preimage_mem_nhdsWithin
        (hU.mem_nhds hmem)] with w hw
      exact supportedAffineGaugeFamily_eq_gauge V b lift η c (hright _ hw)
    exact (affineGaugeFamily_contMDiffWithinAt V b lift η c hU hlift hη hP hz hmem
      (hshift _ ⟨hz.1, hs⟩ _ hz.2)).congr_of_eventuallyEq heq
        (supportedAffineGaugeFamily_eq_gauge V b lift η c (hright _ hmem))
  · have heq : supportedAffineGaugeFamily V b lift η c =ᶠ[𝓝 z]
        fun w => V.squareFamily w.1 w.2 := by
      filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage continuous_fst).mem_nhds
        hs] with w hw
      exact supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c hw
    exact (hbase z hz).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

theorem supportedAffineGaugeFamily_time_closed {P : Set ℝ} (hP : P ⊆ V.parameterDomain)
    (hrec : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, ∀ v ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (lift (V.squareFamily s v)) = V.squareFamily s v)
    {s v : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (hv : v ∈ P) :
    G.spacetime.timeFunction (supportedAffineGaugeFamily V b lift η c (s, v)) = T - s ^ 2 := by
  by_cases ht : s ∈ tsupport η
  · rw [supportedAffineGaugeFamily_eq_gauge V b lift η c (hrec s ⟨hs, ht⟩ v hv)]
    have hclock := ((G.gaugeCover.cylinder b).time_eq (lift (V.squareFamily s v))).symm.trans
      (congrArg G.spacetime.timeFunction (hrec s ⟨hs, ht⟩ v hv))
    simp only [affineGaugeFamily, (G.gaugeCover.cylinder b).time_eq, hclock,
      variation_squareFamily_time V hs (hP hv)]
  · rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c ht,
      variation_squareFamily_time V hs (hP hv)]

theorem supportedAffineGaugeFamily_zero_closed
    (hrec : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (R.curve s)) = R.curve s)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    supportedAffineGaugeFamily V b lift η c (s, 0) = R.curve s := by
  by_cases ht : s ∈ tsupport η
  · have h := hrec s ⟨hs, ht⟩
    have hVrec : (G.gaugeCover.cylinder b).toSpacetime (lift (V.squareFamily s 0)) =
        V.squareFamily s 0 := by rwa [V.square_base]
    rw [supportedAffineGaugeFamily_eq_gauge V b lift η c hVrec]
    simp only [affineGaugeFamily, mul_zero, zero_smul, TopologicalSpace.Opens.affineShift_zero,
      Prod.mk.eta, V.square_base, h]
  · rw [supportedAffineGaugeFamily_eq_of_not_tsupport V b lift η c ht, V.square_base]

end PoincareConjecture.M14
