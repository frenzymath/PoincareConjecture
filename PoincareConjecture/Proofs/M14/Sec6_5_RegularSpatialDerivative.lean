import PoincareConjecture.Proofs.M14.Sec6_5_RegularSmooth
import PoincareConjecture.Proofs.M14.Sec6_3_ActionDifferential
import PoincareConjecture.Proofs.M14.Sec6_3_StablePrefix

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

theorem reducedLengthAt_eq_normalized_action (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (hmin : M14IsMinimizing (E.path Z s hs hpos)) :
    M14ReducedLengthAt G T 0 x (E.gamma Z s) = E.action Z s / (2 * s) := by
  unfold M14ReducedLengthAt
  rw [E.clock Z s hs, sub_sub_cancel, ← E.reduced_length_global_eq Z s hs hpos hmin,
    E.reduced_length_eq Z s hs hpos]

set_option backward.isDefEq.respectTransparency false in

theorem reducedLengthAt_horizontal_differential
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (V : G.Horizontal (E.gamma Z s)) :
    mvfderiv (spacetimeModel n) (M14ReducedLengthAt G T 0 x) (E.gamma Z s) V.val =
      G.spacetime.horizontalMetric.inner (E.gamma Z s)
        (hpoint ▸ (E.square_path Z s hs hpos).horizontal_velocity s) V / (2 * s) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨H, hZH⟩ := jointDomain_stableSet E hz
  have hbij : Function.Bijective (E.differential Z s hs) := by
    have hstable := (H.carrier_exact Z).mp hZH
    unfold M14StableInitialVector at hstable
    rw [Real.sqrt_sq hpos.le] at hstable
    exact hstable.choose_spec.1
  obtain ⟨W, hWV⟩ := hbij.2 V
  have hline : HasDerivAt (fun r : ℝ => Z + r • W) W 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
  have hzero : Z + (0 : ℝ) • W = Z := by simp only [zero_smul, add_zero]
  have hnear : (fun r : ℝ => M14ReducedLengthAt G T 0 x (E.gamma (Z + r • W) s))
      =ᶠ[𝓝 0] (fun r => E.action (Z + r • W) s / (2 * s)) := by
    have hU : H.carrier ∈ 𝓝 (Z + (0 : ℝ) • W) := hzero.symm ▸ H.carrier_open.mem_nhds hZH
    filter_upwards [hline.continuousAt.preimage_mem_nhds hU] with r hr
    have hsurv : (Z + r • W, s) ∈ E.domain := by
      simpa only [Real.sqrt_sq hpos.le] using H.survivor _ hr
    have hbranch := stableInitialVector_unique_branch E ((H.carrier_exact _).mp hr)
    exact reducedLengthAt_eq_normalized_action E hsurv hpos
      (exponentialPath_minimizing_of_uniqueBranch E hpos hsurv hbranch)
  have hq : E.gamma Z s ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) :=
    ⟨⟨(Z, s), hz⟩, rfl⟩
  have hl := ((reducedLengthAt_contMDiffOn_jointImage hM04 hM12 E) _ hq).contMDiffAt
    ((jointMap_range_isOpen E).mem_nhds hq)
  have hgamma := (exponentialFamily_gamma_slice_contMDiffAt E hs).mdifferentiableAt (by simp)
  have hcomp := ((hl.mdifferentiableAt (by simp)).hasMFDerivAt.comp Z hgamma.hasMFDerivAt)
  have hactual := hcomp.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hzero.symm
  change HasDerivAt (fun r : ℝ => M14ReducedLengthAt G T 0 x (E.gamma (Z + r • W) s))
    (mvfderiv (spacetimeModel n) (M14ReducedLengthAt G T 0 x) (E.gamma Z s)
      (M14InitialVectorDerivative G E.gamma s Z W)) 0 at hactual
  rw [← E.differential_pointwise_mfderiv Z s hs W, hWV] at hactual
  have ha := exponentialFamily_action_differential hCoordinates hM04 hM12 E Z s hs hpos
  have haction := ha.1.hasMFDerivAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hzero.symm
  have heq := hactual.unique ((haction.div_const (2 * s)).congr_of_eventuallyEq hnear)
  obtain ⟨_, hpair⟩ := ha.2 W
  have hp := hpair.trans (congrArg (G.spacetime.horizontalMetric.inner (E.gamma Z s)
    (hpoint ▸ (E.square_path Z s hs hpos).horizontal_velocity s)) hWV)
  exact heq.trans (congrArg (fun r : ℝ => r / (2 * s)) hp)

end PoincareConjecture.M14
