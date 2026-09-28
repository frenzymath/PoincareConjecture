import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Connection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Forcing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Equation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

open Poincare.Analysis.Calculus

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem normalizedPotential_chart_eventually_domain
    (z : L.limitCarrier.carrier) (K : Set E) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 3) z).target) :
    ∀ᶠ k in atTop, ∀ x ∈ K, (extChartAt (𝓡 3) z).symm x ∈ L.exhaustion k := by
  let W := AncientPointedGeometricConvergence.window
    (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (J := fun _ => Iio (1 : ℝ)) (T := 1)
    (fun _ => G.unscaledSourceFlow.shrink) L
    (a := -1) (b := 1 / 2) (by norm_num) (by norm_num) 0
    (by intro k t ht; exact ht.2.trans (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨j, hj⟩ := W.exists_exhaustion_superset
    (hK.image_of_continuousOn ((contMDiffOn_extChartAt_symm (n := ∞) z).continuousOn.mono hKt))
  have hmono := monotone_nat_of_le_succ L.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with k hk x hx
  exact hmono hk (hj (mem_image_of_mem _ hx))

theorem normalizedPotentialPullback_coordinate_locally_smooth
    (z : L.limitCarrier.carrier) :
    LocallyEventuallyContDiff (extChartAt (𝓡 3) z).target
      (fun k => G.normalizedPotentialPullback L k ∘ (extChartAt (𝓡 3) z).symm) := by
  intro K hK hKt
  filter_upwards [G.normalizedPotential_chart_eventually_domain L z K hK hKt] with k hk
  let U := (extChartAt (𝓡 3) z).target ∩ (extChartAt (𝓡 3) z).symm ⁻¹' L.exhaustion k
  have hU : IsOpen U := (contMDiffOn_extChartAt_symm (n := ∞) z).continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target z) (L.exhaustion_open k)
  refine ⟨U, hU, fun x hx => ⟨hKt hx, hk x hx⟩, fun x hx => ?_⟩
  exact (contMDiffAt_iff_contDiffAt.mp
    (((G.normalizedPotentialPullback_contMDiffOn L k).contMDiffAt
      ((L.exhaustion_open k).mem_nhds hx.2)).comp x
        ((contMDiffOn_extChartAt_symm (n := ∞) z).contMDiffAt
          ((isOpen_extChartAt_target z).mem_nhds hx.1)))).contDiffWithinAt

theorem normalizedPotentialSpacetimeCoefficients_deriv_time
    (z : L.limitCarrier.carrier) (k : ℕ) (x : E)
    (hx : x ∈ (extChartAt (𝓡 3) z).target)
    (hxk : (extChartAt (𝓡 3) z).symm x ∈ L.exhaustion k) :
    deriv (fun t => G.normalizedPotentialSpacetimeCoefficients L z k (t, x)) 0 =
      fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k) (0, x) (1, 0) := by
  have he := ((L.embedding_smooth k).contMDiffOn.contMDiffAt
    ((L.exhaustion_open k).mem_nhds hxk)).comp x
      ((contMDiffOn_extChartAt_symm (n := ∞) z).contMDiffAt
        ((isOpen_extChartAt_target z).mem_nhds hx))
  have hh := G.unscaledSourceFlow.shrink.smooth.contDiffAt_spacetime_pullbackCoefficients
    isOpen_Iio he (by norm_num : (0 : ℝ) ∈ Iio 1)
  exact ((hh.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))).deriv

theorem normalizedPotentialPullback_coordinate_derivatives_bounded
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : MetricComplete (L.limitFlow.metric 0)) (z : L.limitCarrier.carrier) :
    LocallyEventuallyBoundedDerivatives (extChartAt (𝓡 3) z).target
      (fun k => G.normalizedPotentialPullback L k ∘ (extChartAt (𝓡 3) z).symm) := by
  let f := fun k => G.normalizedPotentialPullback L k ∘ (extChartAt (𝓡 3) z).symm
  let P := fun k x => G.normalizedPotentialSpacetimeCoefficients L z k (0, x)
  obtain ⟨hPs, hPjet⟩ := G.normalizedPotentialCoefficients_smooth_convergence L z
  obtain ⟨hAs, hAb⟩ := locallyEventuallyBoundedDerivatives_potentialConnectionOperator
    (isOpen_extChartAt_target z) hPs ((L.limitFlow.metric 0).contDiffOn_chartCoefficients z)
    (fun x hx => (L.limitFlow.metric 0).isInvertible_chartCoefficients z hx) hPjet
  obtain ⟨hBs, hBb⟩ := G.normalizedPotentialForcing_bounds L hD p hescape z
  apply locallyEventuallyBoundedDerivatives_of_hessian_recurrence
    (A := fun k x => potentialConnectionOperator (P k x, fderiv ℝ (P k) x))
    (B := G.normalizedPotentialForcing L z)
    (G.normalizedPotentialPullback_coordinate_locally_smooth L z) hAs hBs hAb hBb
  · intro K hK hKt
    obtain ⟨B, _, hB⟩ := G.normalizedPotentialPullback_eventually_coordinate_C1_bounded
      L hD p hescape hcomplete z K hK hKt
    exact ⟨B, hB.mono fun k hk x hx => (hk x hx).1⟩
  · intro K hK hKt
    obtain ⟨B, _, hB⟩ := G.normalizedPotentialPullback_eventually_coordinate_C1_bounded
      L hD p hescape hcomplete z K hK hKt
    exact ⟨B, hB.mono fun k hk x hx => (hk x hx).2⟩
  · intro K hK hKt
    filter_upwards [G.normalizedPotential_chart_eventually_domain L z K hK hKt] with k hk x hx
    have hneigh : IsOpen ((extChartAt (𝓡 3) z).target ∩
        (extChartAt (𝓡 3) z).symm ⁻¹' L.exhaustion k) :=
      (contMDiffOn_extChartAt_symm (n := ∞) z).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target z) (L.exhaustion_open k)
    filter_upwards [hneigh.mem_nhds ⟨hKt hx, hk x hx⟩] with y hy
    ext v w
    simp only [add_apply]
    rw [potentialConnectionOperator_apply]
    have heq := G.normalizedPotentialPullback_fderiv2 L z k y hy.1 hy.2 v w
    dsimp only at heq
    rw [G.normalizedPotentialSpacetimeCoefficients_deriv_time L z k y hy.1 hy.2] at heq
    simpa only [normalizedPotentialForcing, add_apply,
      smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using heq

end PoincareConjecture.ShrinkingSolitonFlow
