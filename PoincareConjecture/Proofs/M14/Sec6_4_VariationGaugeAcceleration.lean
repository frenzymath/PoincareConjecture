import PoincareConjecture.Proofs.M14.Sec6_4_VariationGauge
import PoincareConjecture.Proofs.M14.Sec6_4_GaugeCovariantFields
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackRestriction
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence

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

private theorem acceleration_transport_heq {q r : G.Point} (h : q = r)
    (v : G.Horizontal q) : HEq (h.symm ▸ v : G.Horizontal r) v := by
  cases h
  rfl

theorem variationEndpointAcceleration_gauge
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    (b : G.gaugeCover.index)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (x₀ : G.gaugeCover.spatial b) {S P : Set ℝ}
    (hS : S ⊆ M14SqrtParameterInterval τ₁ τ₂) (hP : IsOpen P)
    (hzero : (0 : ℝ) ∈ P) (hPsub : P ⊆ V.parameterDomain)
    {β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β (S ×ˢ P))
    (hrec : ∀ r ∈ S, ∀ u ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
    (hclock : ∀ r ∈ S, ∀ u ∈ P, (β (r, u)).1.val = T - r ^ 2)
    {s : ℝ} (hs : s ∈ S) :
    HEq (M14VariationEndpointAcceleration V D s (hS hs))
      ((G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2
        (deriv (deriv (fun v => (β (s, v)).2.val)) 0 +
          M08.closedChartConnection W.flow T x₀ S (s, (β (s, 0)).2.val)
            (deriv (fun v => (β (s, v)).2.val) 0)
            (deriv (fun v => (β (s, v)).2.val) 0))) := by
  let γ := fun u => (G.gaugeCover.cylinder b).toSpacetime (β (s, u))
  let Y : ∀ u, G.Horizontal (γ u) := fun u =>
    (G.gaugeCover.metric b).spatialTangentEquiv (β (s, u)).1 (β (s, u)).2
      (deriv (fun v => (β (s, v)).2.val) u)
  let E := pullbackExtensionRestrict (D.endpoint_extension s (hS hs)) hPsub
  have hγ : EqOn (fun u => V.squareFamily s u) γ P :=
    fun u hu => (hrec s hs u hu).symm
  have hY : ∀ u ∈ P, HEq (M14EndpointVariationField V s u) (Y u) :=
    fun u hu => endpointVariationField_gauge V b hP hβ hrec hs hu
  let E' := pullbackExtensionCongrOn E hγ hY
  have hcurve := hβ.comp ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn
    (fun _ hr => ⟨hs, hr⟩)
  have htime (r : ℝ) (hr : r ∈ S) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr 0 hzero]
    exact (β (r, 0)).1.property
  have hc := horizontalCovariantDerivative_gauge_coefficient b hCoordinates W T x₀ htime
    (β := fun u => β (s, u)) E' hzero (hP.uniqueDiffOn 0 hzero)
    ((hcurve 0 hzero).mdifferentiableWithinAt (by simp)) hs (hclock s hs 0 hzero)
  have hform : M14HorizontalCovariantDerivative G γ P Y E' 0 =
      (G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2
        (deriv (deriv (fun v => (β (s, v)).2.val)) 0 +
          M08.closedChartConnection W.flow T x₀ S (s, (β (s, 0)).2.val)
            (deriv (fun v => (β (s, v)).2.val) 0)
            (deriv (fun v => (β (s, v)).2.val) 0)) := by
    apply ((G.gaugeCover.metric b).spatialTangentEquiv (β (s, 0)).1 (β (s, 0)).2).symm.injective
    simpa only [Y, ContinuousLinearEquiv.symm_apply_apply,
      derivWithin_of_mem_nhds (hP.mem_nhds hzero)] using hc
  exact (acceleration_transport_heq (V.square_base s) _).trans
    ((heq_of_eq (horizontalCovariantDerivative_restrict
      (D.endpoint_extension s (hS hs)) hPsub (hP.mem_nhds hzero))).trans
      ((horizontalCovariantDerivative_congrOn E hγ hY hzero).trans (heq_of_eq hform)))

end PoincareConjecture.M14
