import PoincareConjecture.Proofs.M14.Sec6_3_InitialVectorVariation
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVariationFields
import PoincareConjecture.Proofs.M14.Sec6_3_ActionFirstVariation
import PoincareConjecture.Proofs.M14.Sec6_2_VariationActionComparison
import PoincareConjecture.Statements.M14Exponential

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

private theorem inner_transport_heq {q r : G.Point} (h : q = r)
    (A Y : G.Horizontal q) (W : G.Horizontal r) (hY : HEq Y W) :
    G.spacetime.horizontalMetric.inner q A Y =
      G.spacetime.horizontalMetric.inner r (h ▸ A) W := by
  cases h
  cases hY
  rfl

theorem initialVectorVariation_action (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (V : M14LVariationData G (E.path Z s hs hpos) (E.square_path Z s hs hpos))
    (hmem : ∀ u ∈ V.parameterDomain, (Z + u • W, s) ∈ E.domain)
    (hV : ∀ r ∈ M14SqrtParameterInterval 0 (s ^ 2), ∀ u,
      V.squareFamily r u = E.gamma (Z + u • W) r)
    {u : ℝ} (hu : u ∈ V.parameterDomain) :
    M14VariationAction V u = E.action (Z + u • W) s := by
  rw [E.action_eq _ _ (hmem u hu) hpos]
  apply variationAction_eq_of_squareFamily V (E.square_path _ _ (hmem u hu) hpos) hu
  intro r hr
  exact (hV r hr u).trans (exponential_square_curve_eq E _ (hmem u hu) hpos hr).symm

theorem exponentialFamily_action_differential
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x) (s : ℝ)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    MDifferentiableAt (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ)) (fun A => E.action A s) Z ∧
      ∀ W : G.Horizontal x,
        ∃ h : (E.square_path Z s hs hpos).curve s = E.gamma Z s,
          mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ)) (fun A => E.action A s) Z W =
            G.spacetime.horizontalMetric.inner (E.gamma Z s)
              (h ▸ (E.square_path Z s hs hpos).horizontal_velocity s)
              (E.differential Z s hs W) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hdiff := (exponentialFamily_action_slice_contMDiffAt hM04 hM12 E hs hpos).mdifferentiableAt
    (by simp)
  refine ⟨hdiff, ?_⟩
  intro W
  let dA : G.Horizontal x →L[ℝ] ℝ :=
    mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ)) (fun A => E.action A s) Z
  change ∃ h : (E.square_path Z s hs hpos).curve s = E.gamma Z s,
    dA W = G.spacetime.horizontalMetric.inner (E.gamma Z s)
      (h ▸ (E.square_path Z s hs hpos).horizontal_velocity s) (E.differential Z s hs W)
  obtain ⟨V, hmem, hV⟩ := exists_initialVectorVariation hM04 hM12 E Z W hs hpos

  set_option backward.isDefEq.respectTransparency false in
    have hzfield : M14VariationField V (Real.sqrt (0 : ℝ)) = 0 :=
      Eq.mpr (congrArg (fun r : ℝ => M14VariationField V r = 0) Real.sqrt_zero)
        (initialVectorVariation_field_zero E Z W hs hpos V hV)
    have hfirst₀ := firstVariation_euler_fixedInitial hCoordinates hM12
      (E.square_extension Z s hs hpos) (E.square_euler Z s hs hpos) V hzfield
    have hfirst : HasDerivAt (M14VariationAction V)
        (G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve s)
          ((E.square_path Z s hs hpos).horizontal_velocity s) (M14VariationField V s)) 0 :=
      Eq.mp (congrArg (fun r : ℝ => HasDerivAt (M14VariationAction V)
        (G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve r)
          ((E.square_path Z s hs hpos).horizontal_velocity r) (M14VariationField V r)) 0)
            (Real.sqrt_sq hpos.le)) hfirst₀
    have hsC : s ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
      simp only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le, mem_Icc]
      exact ⟨hpos.le, le_rfl⟩
    let h := exponential_square_curve_eq E Z hs hpos hsC
    have hfield := initialVectorVariation_field_terminal E Z W hs hpos V hV
    rw [inner_transport_heq h _ _ _ hfield] at hfirst
    have hzero : (0 : ℝ) ∈ V.parameterDomain := by
      rw [V.parameterDomain_eq]
      exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
    have hparameter : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
    have hfirst' : HasDerivAt (fun u : ℝ => E.action (Z + u • W) s)
        (G.spacetime.horizontalMetric.inner (E.gamma Z s)
          (h ▸ (E.square_path Z s hs hpos).horizontal_velocity s) (E.differential Z s hs W)) 0 := by
      apply hfirst.congr_of_eventuallyEq
      filter_upwards [hparameter.mem_nhds hzero] with u hu
      exact (initialVectorVariation_action E Z W hs hpos V hmem hV hu).symm
    have hline : HasDerivAt (fun u : ℝ => Z + u • W) W 0 := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
    have hactual := hdiff.hasMFDerivAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
      (by simp only [zero_smul, add_zero])
    exact ⟨h, hactual.unique hfirst'⟩

theorem actionDifferentialStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14ActionDifferentialStatement G := by
  intro T x E
  exact ⟨exponentialFamily_action_smooth hM04 hM12 E,
    exponentialFamily_action_differential hCoordinates hM04 hM12 E⟩

end PoincareConjecture.M14
