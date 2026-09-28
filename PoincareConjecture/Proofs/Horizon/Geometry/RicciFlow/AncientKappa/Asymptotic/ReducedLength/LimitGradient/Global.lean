import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitGradient.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.LimitRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Lipschitz


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem reducedLengthPullback_limit_intrinsic_gradient_bound_in_coordinates_ae
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {a : EuclideanSpace ℝ (Fin n)} {r τ : ℝ}
    (hr : 0 < r) (hτ : 0 < τ)
    (hchart : Metric.closedBall a (2 * r) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    ∀ᵐ x ∂volume.restrict (Metric.ball a (r / 2)),
      ((G.limit.flow.metric (-τ)).tangentNorm (e x)
        ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) (e x))) ^ 2 ≤
        3 * l (e x, τ) / τ := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let f := fun y => l (y, τ)
  have hUC : Metric.ball a (r / 2) ⊆ Metric.closedBall a r :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall
  have hUs : Metric.ball a (r / 2) ⊆ e.source :=
    hUC.trans ((Metric.closedBall_subset_closedBall (by linarith)).trans hchart)
  obtain ⟨L, hL⟩ := G.reducedLengthPullback_limit_lipschitz_on_chart_cylinder
    P hσ l hlim q hr hτ (le_refl τ) hchart
  have hv : LipschitzOnWith L (f ∘ e) (Metric.ball a (r / 2)) := by
    simpa only [Function.comp_def, mul_one] using hL.comp
      (LipschitzWith.prodMk_right τ).lipschitzOnWith
      (fun x hx => ⟨hUC hx, le_refl τ, le_refl τ⟩)
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨(contMDiffOn_chart_symm (n := ∞)).mdifferentiableOn (by simp),
      (contMDiffOn_chart (n := ∞)).mdifferentiableOn (by simp)⟩
  filter_upwards [G.reducedLengthPullback_limit_coordinate_gradient_bound_ae
      P hσ l hlim q hr hτ hchart,
    ae_restrict_of_ae (Poincare.Analysis.WeakDerivative.ae_differentiableAt_of_lipschitzOn
      volume Metric.isOpen_ball hv), ae_restrict_mem measurableSet_ball] with x hx hd hxs
  have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f ∘ e) (e.symm (e x)) := by
    rw [e.left_inv (hUs hxs)]
    exact (hd hxs).hasFDerivAt.hasMFDerivAt.mdifferentiableAt
  have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e x) := by
    apply (hf'.comp (e x) (hD.symm.mdifferentiableAt
      (e.map_source (hUs hxs)))).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds (e.map_source (hUs hxs))] with y hy
    simp only [Function.comp_apply, e.right_inv hy]
  rw [(G.limit.flow.connection (-τ)).gradient_norm_sq_eq_inverse_pairing e
    contMDiffOn_chart_symm contMDiffOn_chart (hUs hxs) hf]
  exact hx



theorem reducedLengthPullback_limit_gradient_bound_ae
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ))) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᵐ x ∂(G.limit.flow.metric (-τ)).volumeMeasure,
      ((G.limit.flow.metric (-τ)).tangentNorm x
        ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)) ^ 2 ≤
        3 * l (x, τ) / τ := by
  classical
  let g := G.limit.flow.metric (-τ)
  let B := fun x => (g.tangentNorm x
    ((G.limit.flow.connection (-τ)).gradient (fun y => l (y, τ)) x)) ^ 2 ≤
      3 * l (x, τ) / τ
  have hrad (q : G.limit.carrier.carrier) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) (2 * r) ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) q).target := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
      (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target
      ((chartAt (EuclideanSpace ℝ (Fin n)) q) q)
      ((chartAt (EuclideanSpace ℝ (Fin n)) q).map_source (mem_chart_source _ q))
    refine ⟨δ / 4, by positivity, ?_⟩
    intro x hx
    apply hball
    change dist x ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) < δ
    have hd : dist x ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) ≤ 2 * (δ / 4) := hx
    linarith
  choose r hr hchart using hrad
  let U := fun q : G.limit.carrier.carrier =>
    (chartAt (EuclideanSpace ℝ (Fin n)) q).source ∩
      (chartAt (EuclideanSpace ℝ (Fin n)) q) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) q) q) (r q / 2)
  have hU (q : G.limit.carrier.carrier) : IsOpen (U q) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) q).continuousOn.isOpen_inter_preimage
      (chartAt (EuclideanSpace ℝ (Fin n)) q).open_source Metric.isOpen_ball
  have hcover : (univ : Set G.limit.carrier.carrier) ⊆ ⋃ q, U q := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source _ x,
      Metric.mem_ball_self (div_pos (hr x) (by norm_num : (0 : ℝ) < 2))⟩
  have hae (q : G.limit.carrier.carrier) : ∀ᵐ y ∂g.volumeMeasure, y ∈ U q → B y := by
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    have hlocal := (ae_restrict_iff' measurableSet_ball).mp
      (G.reducedLengthPullback_limit_intrinsic_gradient_bound_in_coordinates_ae
        P hσ l hlim q (hr q) hτ (hchart q))
    have hcoord : ∀ᵐ x ∂volume.restrict e.source, e x ∈ U q → B (e x) := by
      filter_upwards [ae_restrict_of_ae hlocal, ae_restrict_mem e.open_source.measurableSet]
        with x hx hxs hxU
      apply hx
      have hh := hxU.2
      change e.symm (e x) ∈ Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) q) q)
        (r q / 2) at hh
      rwa [e.left_inv hxs] at hh
    have h := (ae_restrict_iff' e.open_target.measurableSet).mp
      (g.ae_restrict_of_ae_pullback e contMDiffOn_chart_symm contMDiffOn_chart
        (P := fun y => y ∈ U q → B y) hcoord)
    filter_upwards [h] with y hy hyU
    exact hy hyU.1 hyU
  obtain ⟨s, hs, hsc⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable s := hs.to_subtype
  have hall : ∀ᵐ x ∂g.volumeMeasure, ∀ i : s, x ∈ U i → B x :=
    ae_all_iff.mpr (fun i => hae i)
  filter_upwards [hall] with x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hsc (mem_univ x))
  exact hx ⟨i, hi⟩ hxi

end PoincareConjecture.AncientCompactTimeConvergence
