import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Terminal.Closeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Embedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_buffered_terminal_epsilonNeck_threshold
    (hC : RicciFlowCurvatureTheory.{u}) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ η : ℝ, 0 < η ∧
      ∀ {a b : ℝ} {S : PointedFlowSequence 3 a b}
        (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b),
        G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) →
      ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
        (q : UnitTwoSphere) (_hq : Φ (q, 0) = G.limitFlow.base)
        (C : ℕ → FlowCarrier.{u} 3) (I : ℕ → Set ℝ)
        (F : ∀ k, RicciFlow 3 (C k).carrier (I k))
        (Ψ : ∀ k, (S.carrier k).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (C k).carrier)
        (A radius : ℕ → ℝ),
        Tendsto A atTop atTop → Tendsto radius atTop atTop →
        (∀ k, IsOpen (I k)) →
        (∀ k, Icc (-A k) 0 ⊆ interior (I k)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
          ((F k).connection t).NonnegativeCurvatureOperator x) →
        (∀ k, ∀ t ∈ Icc (-A k) 0,
          ∀ x ∈ ((F k).metric 0).ball (Ψ k (S.flow k).base) (radius k),
            ((F k).connection t).scalarCurvature x ≤ 4) →
        (∀ k, ((F k).connection 0).scalarCurvature (Ψ k (S.flow k).base) = 1) →
      ∀ {δ s : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ η →
        (1 / 2 : ℝ) ≤ s → s ≤ 1 → 1 - s ≤ D * δ →
        (∀ k, ∀ (x : (S.carrier k).carrier) (v w : TangentSpace (𝓡 3) x),
          ((S.flow k).metricAt 0).inner x v w =
            ((F k).metric (-δ)).inner (Ψ k x)
              (mfderiv (𝓡 3) (𝓡 3) (Ψ k) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Ψ k) x w)) →
        (fun z v w => s * roundCylinderPullback (G.limitFlow.metricAt 0) Φ z v w) =
          EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop,
          let e := (G.cylinderSlabEmbedding hzero Φ ε i).trans
            (Ψ (G.subsequence i)).toHomeomorph.toOpenPartialHomeomorph
          ∃ N : EpsilonNeck ((F (G.subsequence i)).metric 0),
            N.epsilon = ε ∧ N.scale = 1 ∧
            N.center = Ψ (G.subsequence i) (S.flow (G.subsequence i)).base ∧
            N.connection = (F (G.subsequence i)).connection 0 ∧
            N.coordinate_map =
              (fun z => Ψ (G.subsequence i) (((G.embedding i).toFun (0, Φ z)).2)) ∧
            N.carrier = e.target ∧ N.coordinate_inverse = e.symm := by
  obtain ⟨η, hη, hclose⟩ :=
    exists_buffered_terminal_cylinder_closeness_threshold hC hε hD
  refine ⟨η, hη, ?_⟩
  intro a b S G hzero hcomplete Φ q hq C I F Ψ A radius
    hA hradius hopen hI hcompleteF hoperator hscalar hnormalize
    δ s hδ hδone hδη hs hsone hgap hmetric hround
  have hc := hclose G hzero hcomplete Φ C I F Ψ A radius hA hradius hopen hI
    hcompleteF hoperator hscalar hδ hδone hδη hs hsone hgap hmetric hround
  filter_upwards [hc, G.eventually_cylinderSlabEmbedding hzero Φ hε] with i hc he
  let e₀ := G.cylinderSlabEmbedding hzero Φ ε i
  let e := e₀.trans (Ψ (G.subsequence i)).toHomeomorph.toOpenPartialHomeomorph
  have hemap : (e : RoundCylinderSpace → (C (G.subsequence i)).carrier) =
      (fun z => Ψ (G.subsequence i) (((G.embedding i).toFun (0, Φ z)).2)) := rfl
  obtain ⟨hsource₀, hsmooth₀, hinverse₀, _⟩ := he
  have hsource : e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ := by
    change e₀.source ∩ e₀ ⁻¹' univ = _
    rw [preimage_univ, inter_univ]
    exact hsource₀
  have hsmooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) := by
    intro z hz
    exact ((Ψ (G.subsequence i)).contMDiff.contMDiffAt.comp_contMDiffWithinAt
      z (hsmooth₀ z hz))
  have hinverse : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
    intro x hx
    have hx₀ : (Ψ (G.subsequence i)).symm x ∈ e₀.target := by
      change x ∈ univ ∩ (Ψ (G.subsequence i)).symm ⁻¹' e₀.target at hx
      exact hx.2
    exact ((hinverse₀.contMDiffAt (e₀.open_target.mem_nhds hx₀)).comp
      x ((Ψ (G.subsequence i)).symm.contMDiff x)).contMDiffWithinAt
  have hcentral : e '' (univ ×ˢ ({0} : Set ℝ)) ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    apply e.map_source
    rw [hsource]
    have hpos := inv_pos.mpr hε
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ from ⟨neg_neg_of_pos hpos, hpos⟩)⟩
  refine ⟨{
    epsilon := ε
    epsilon_pos := hε
    epsilon_lt_half := hεhalf
    scale := 1
    scale_pos := zero_lt_one
    center := Ψ (G.subsequence i) (S.flow (G.subsequence i)).base
    connection := (F (G.subsequence i)).connection 0
    scalar_center_pos := by rw [hnormalize]; exact zero_lt_one
    scale_eq_scalar := by rw [hnormalize, Real.one_rpow]
    carrier := e.target
    carrier_open := e.open_target
    coordinate := neckDomainCoordinates e hsource
    coordinate_map := e
    coordinate_map_eq := fun z => rfl
    coordinate_map_smooth := hsmooth
    coordinate_inverse := e.symm
    coordinate_inverse_mem := fun x hx => neckDomainCoordinates_inverse_mem e hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left e hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right e hsource
    coordinate_inverse_smooth := hinverse
    central_sphere := e '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := ?_
    central_sphere_subset := hcentral
    metric_comparison := ⟨by
      simpa only [inv_one, one_pow, one_mul, hemap] using hc⟩
  }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨(q, 0), ⟨mem_univ _, mem_singleton _⟩, ?_⟩
  change Ψ (G.subsequence i) (G.cylinderSlabEmbedding hzero Φ ε i (q, 0)) = _
  rw [G.cylinderSlabEmbedding_center hzero Φ ε i q hq]

end PoincareConjecture.PointedGeometricConvergence
