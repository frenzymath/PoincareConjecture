import PoincareConjecture.Proofs.M14.Sec6_2_SupportedGaugeFamily

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

theorem gaugeShiftFamily_contMDiffWithinAt {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η) {P : Set ℝ} {z : ℝ × ℝ}
    (hs : z.1 ∈ M14SqrtParameterInterval τ₁ τ₂) (hz : R.curve z.1 ∈ U)
    (hshift : (lift (R.curve z.1)).2.val + z.2 • η z.1 ∈ G.gaugeCover.spatial b) :
    ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (gaugeShiftFamily R b lift η) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) z := by
  have hR : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun w : ℝ × ℝ => R.curve w.1) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) z :=
    (R.smooth.mono R.interval_subset _ hs).comp z contMDiffWithinAt_fst
      (fun _ hw => hw.1)
  have hL := ((hlift _ hz).contMDiffAt (hU.mem_nhds hz)).comp_contMDiffWithinAt z hR
  have hv : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun w : ℝ × ℝ => w.2 • η w.1)
      (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) z :=
    contMDiffWithinAt_snd.smul
      (hη.contMDiff.contMDiffAt.comp_contMDiffWithinAt z contMDiffWithinAt_fst)
  have hS := (((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hshift).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hshift)).comp_contMDiffWithinAt
      z (hL.snd.prodMk hv)
  exact (G.gaugeCover.cylinder b).smooth.contMDiffAt.comp_contMDiffWithinAt z
    (hL.fst.prodMk hS)

theorem supportedGaugeFamily_contMDiffOn_closed {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, R.curve s ∈ U)
    {P : Set ℝ}
    (hshift : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ tsupport η, ∀ v ∈ P,
      (lift (R.curve s)).2.val + v • η s ∈ G.gaugeCover.spatial b) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (supportedGaugeFamily R b lift η) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) := by
  have hbase : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => R.curve z.1) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) :=
    (R.smooth.mono R.interval_subset).comp contMDiffOn_fst (fun _ hz => hz.1)
  intro z hz
  by_cases hs : z.1 ∈ tsupport η
  · have hmem := hsrc z.1 ⟨hz.1, hs⟩
    have heq : supportedGaugeFamily R b lift η
        =ᶠ[𝓝[M14SqrtParameterInterval τ₁ τ₂ ×ˢ P] z] gaugeShiftFamily R b lift η := by
      filter_upwards [(hbase z hz).continuousWithinAt.preimage_mem_nhdsWithin
        (hU.mem_nhds hmem)] with w hw
      exact supportedGaugeFamily_eq_gauge R b lift η (hright _ hw)
    exact (gaugeShiftFamily_contMDiffWithinAt R b lift η hU hlift hη hz.1 hmem
      (hshift _ ⟨hz.1, hs⟩ _ hz.2)).congr_of_eventuallyEq heq
        (supportedGaugeFamily_eq_gauge R b lift η (hright _ hmem))
  · have heq : supportedGaugeFamily R b lift η =ᶠ[𝓝 z] fun w => R.curve w.1 := by
      filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage continuous_fst).mem_nhds
        hs] with w hw
      exact supportedGaugeFamily_eq_of_not_tsupport R b lift η hw
    exact (hbase z hz).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

end PoincareConjecture.M14
