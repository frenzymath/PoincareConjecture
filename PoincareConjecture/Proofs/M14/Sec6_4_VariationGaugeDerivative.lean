import PoincareConjecture.Proofs.M14.Sec6_4_VariationGaugeAcceleration

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

private theorem field_transport_heq {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : HEq (h.symm ▸ v : G.Horizontal r) v := by
  cases h
  rfl

theorem variationField_gauge (V : M14LVariationData G p R)
    (b : G.gaugeCover.index) {S P : Set ℝ} (hP : IsOpen P) (hzero : (0 : ℝ) ∈ P)
    {β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β (S ×ˢ P))
    (hrec : ∀ r ∈ S, ∀ u ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
    {s : ℝ} (hs : s ∈ S) :
    HEq (M14VariationField V s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2
        (deriv (fun v => (β (s, v)).2.val) 0)) :=
  (field_transport_heq (V.square_base s) _).trans
    (endpointVariationField_gauge V b hP hβ hrec hs hzero)

theorem variationCovariantDerivative_gauge
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (b : G.gaugeCover.index)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (x₀ : G.gaugeCover.spatial b) {N P : Set ℝ}
    (hN : IsOpen N) (hP : IsOpen P) (hzero : (0 : ℝ) ∈ P)
    {β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
      ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P))
    (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
    (hclock : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
      (β (r, u)).1.val = T - r ^ 2)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N) :
    HEq (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval τ₁ τ₂)
        (M14VariationField V) D.variation_extension s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2
        (derivWithin (fun r => deriv (fun v => (β (r, v)).2.val) 0)
            (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s +
          M08.closedChartConnection W.flow T x₀ (M14SqrtParameterInterval τ₁ τ₂ ∩ N)
            (s, (β (s, 0)).2.val)
            (derivWithin (fun r => (β (r, 0)).2.val) (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s)
            (deriv (fun v => (β (s, v)).2.val) 0))) := by
  let S := M14SqrtParameterInterval τ₁ τ₂ ∩ N
  let γ := fun r => (G.gaugeCover.cylinder b).toSpacetime (β (r, 0))
  let Y : ∀ r, G.Horizontal (γ r) := fun r =>
    (G.gaugeCover.metric b).spatialTangentEquiv (β (r, 0)).1 (β (r, 0)).2
      (deriv (fun v => (β (r, v)).2.val) 0)
  let E := pullbackExtensionRestrict D.variation_extension (K := S) inter_subset_left
  have hγ : EqOn R.curve γ S := fun r hr =>
    ((hrec r hr 0 hzero).trans (V.square_base r)).symm
  have hY : ∀ r ∈ S, HEq (M14VariationField V r) (Y r) :=
    fun r hr => variationField_gauge V b hP hzero hβ hrec hr
  let E' := pullbackExtensionCongrOn E hγ hY
  have hcurve := hβ.comp (contMDiff_id.prodMk (contMDiff_const (c := (0 : ℝ)))).contMDiffOn
    (fun _ hr => ⟨hr, hzero⟩)
  have hS : UniqueDiffOn ℝ S :=
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).inter hN
  have hc := horizontalCovariantDerivative_gauge_chart b hCoordinates W T x₀
    (β := fun r => β (r, 0)) (fun r hr => hclock r hr 0 hzero) E' hs (hS s hs)
    ((hcurve s hs).mdifferentiableWithinAt (by simp))
  have hform : M14HorizontalCovariantDerivative G γ S Y E' s =
      (G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2
        (derivWithin (fun r => deriv (fun v => (β (r, v)).2.val) 0) S s +
          M08.closedChartConnection W.flow T x₀ S (s, (β (s, 0)).2.val)
            (derivWithin (fun r => (β (r, 0)).2.val) S s)
            (deriv (fun v => (β (s, v)).2.val) 0)) := by
    apply ((G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2).symm.injective
    simpa only [Y, ContinuousLinearEquiv.symm_apply_apply] using hc
  exact (heq_of_eq (horizontalCovariantDerivative_restrict_inter D.variation_extension
    (hN.mem_nhds hs.2))).trans
      ((horizontalCovariantDerivative_congrOn E hγ hY hs).trans (heq_of_eq hform))

end PoincareConjecture.M14
