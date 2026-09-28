import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Terminal.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Terminal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.secondCountable
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

theorem exists_buffered_terminal_cylinder_closeness_threshold
    (hC : RicciFlowCurvatureTheory.{u}) {ε : ℝ} (hε : 0 < ε)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ η : ℝ, 0 < η ∧
      ∀ {a b : ℝ} {S : PointedFlowSequence 3 a b}
        (G : PointedGeometricConvergence S), a < 0 ∧ 0 < b →
        G.limitCarrier.metricComplete (G.limitFlow.metricAt 0) →
      ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
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
      ∀ {δ s : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ η →
        (1 / 2 : ℝ) ≤ s → s ≤ 1 → 1 - s ≤ D * δ →
        (∀ k, ∀ (x : (S.carrier k).carrier) (v w : TangentSpace (𝓡 3) x),
          ((S.flow k).metricAt 0).inner x v w =
            ((F k).metric (-δ)).inner (Ψ k x)
              (mfderiv (𝓡 3) (𝓡 3) (Ψ k) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Ψ k) x w)) →
        (fun z v w => s * roundCylinderPullback (G.limitFlow.metricAt 0) Φ z v w) =
          EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, RoundCylinderClose ε 0
          (roundCylinderPullback ((F (G.subsequence i)).metric 0)
            (fun z => Ψ (G.subsequence i) (((G.embedding i).toFun (0, Φ z)).2))) := by
  let J := Icc (-ε⁻¹) ε⁻¹
  let d : ℕ := ⌊ε⁻¹⌋₊
  have hJ : IsCompact J := isCompact_Icc
  obtain ⟨C₀, Z, hC₀, hZ, hcompare⟩ :=
    exists_roundCylinder_buffered_comparison_constants hJ d
  obtain ⟨B, hB, hterminal⟩ := exists_terminal_cylinder_parametrized_jet_constant hC hJ d
  obtain ⟨η, hη, htolerance⟩ := exists_roundCylinder_terminal_error_tolerance
    hε hC₀ (show 0 ≤ B + 2 * D * Z by positivity)
  refine ⟨η, hη, ?_⟩
  intro a b S G hzero hcomplete Φ C I F Ψ A radius hA hradius hopen hI
    hcompleteF hoperator hscalar δ s hδ hδone hδη hs hsone hgap hmetric hround
  have htime := hterminal G hzero hcomplete Φ C I F Ψ A radius
    hA hradius hopen hI hcompleteF hoperator hscalar hδ hδone hs hsone hmetric hround
  let K : Set RoundCylinderCoordinates := {0} ×ˢ J
  have hK : IsCompact K := isCompact_singleton.prod hJ
  have hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ := by
    rintro x ⟨hx, _⟩
    exact ⟨by simpa only [mem_singleton_iff.mp hx] using
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)), mem_univ _⟩
  have hinitial := G.eventually_cylinder_parametrized_model_error_jets
    hzero Φ.contMDiff hzero (by linarith : 0 < s) hround hK hKU d hη
  filter_upwards [htime, hinitial, G.eventually_cylinderSlabEmbedding hzero Φ hε]
    with i ht hi he
  let e₀ := G.cylinderSlabEmbedding hzero Φ ε i
  let f : RoundCylinderSpace → (C (G.subsequence i)).carrier :=
    fun z => Ψ (G.subsequence i) (((G.embedding i).toFun (0, Φ z)).2)
  let U : Set RoundCylinderSpace := univ ×ˢ Ioo (-ε⁻¹) ε⁻¹
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U := by
    intro z hz
    exact ((Ψ (G.subsequence i)).contMDiff.contMDiffAt.comp z
      (he.2.1.contMDiffAt (hU.mem_nhds hz))).contMDiffWithinAt
  have hsmooth : RoundCylinderTensorSmoothOn ε
      (roundCylinderPullback ((F (G.subsequence i)).metric 0) f) := by
    simpa only [one_mul] using roundCylinderTensorSmoothOn_smul_pullback
      ((F (G.subsequence i)).metric 0) hf 1
  refine ⟨hsmooth, ε ^ 2 / 4, by nlinarith [sq_pos_of_pos hε], ?_⟩
  intro z hz
  have hzU : z ∈ U := ⟨mem_univ _, hz⟩
  have hzJ : z.2 ∈ J := ⟨hz.1.le, hz.2.le⟩
  apply (hcompare ((F (G.subsequence i)).metric (-δ))
    ((F (G.subsequence i)).metric 0) hU hf z hzU hzJ hs hsone hD hδ.le hB hη.le
      hgap ?_ ?_).trans (htolerance hδ.le hδη)
  · intro j hj
    let e : RoundCylinderCoordinates → (S.carrier (G.subsequence i)).carrier :=
      fun y => ((G.embedding i).toFun
        (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm y.1, y.2))).2
    have hcoeff := RiemannianMetric.parametrizedCoefficients_diffeomorph
      ((S.flow (G.subsequence i)).metricAt 0) ((F (G.subsequence i)).metric (-δ))
      (Ψ (G.subsequence i)) (hmetric (G.subsequence i)) e
    change ‖iteratedFDeriv ℝ j
      (((F (G.subsequence i)).metric (-δ)).parametrizedCoefficients (Ψ (G.subsequence i) ∘ e))
      (0, z.2) - s⁻¹ • iteratedFDeriv ℝ j roundCylinderModelCoefficients (0, z.2)‖ ≤ η
    rw [← hcoeff]
    exact hi j hj z.1 (0, z.2) ⟨rfl, hzJ⟩
  · intro j hj
    exact ht z.1 z.2 hzJ j hj

end PoincareConjecture.PointedGeometricConvergence
