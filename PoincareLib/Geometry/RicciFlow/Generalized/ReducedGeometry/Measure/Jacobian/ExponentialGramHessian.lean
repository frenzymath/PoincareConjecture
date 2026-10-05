import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.ExponentialGramHessianChain
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Construction.ExponentialGramVariation
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Differential.ExponentialJacobiField
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialJacobi

/-!
# The actual exponential Jacobi boundary pair is the raw Hessian

Stable nearby branches realize equality of action and endpoint value.
Second variation cancels terminal acceleration, and Green's identity
retains precisely the actual Jacobi boundary pair. Morgan-Tian
Proposition 6.33, pp. 120-121, and Lemma 6.40, pp. 126-127.
-/

set_option autoImplicit false
-- The canonical initial-value path retains the supplied square path definitionally.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_momentum_transport {q r : G.Point} (h : q = r)
    (f : G.Point → ℝ) (A : G.Horizontal q) (c : ℝ)
    (hd : ∀ W : G.Horizontal r,
      mvfderiv (spacetimeModel n) f r W.val =
        G.spacetime.horizontalMetric.inner r (h ▸ A) W / c) :
    ∀ W : G.Horizontal q, mvfderiv (spacetimeModel n) f q W.val =
      G.spacetime.horizontalMetric.inner q A W / c := by
  cases h
  exact hd

private theorem hessian_pair_parameter_congr (γ : ℝ → G.Point)
    (Y : ∀ r, G.Horizontal (γ r)) (f : G.Point → ℝ) {r s T τ : ℝ} (h : r = s)
    (hr : G.spacetime.timeFunction (γ r) = T - τ)
    (hs : G.spacetime.timeFunction (γ s) = T - τ) :
    M14ReducedLengthHessianPairing G ⟨γ r, hr⟩ f (Y r) (Y r) =
      M14ReducedLengthHessianPairing G ⟨γ s, hs⟩ f (Y s) (Y s) := by
  subst s
  rfl

/-- At a joint endpoint, the actual normalized exponential Jacobi
field attains the raw reduced-length Hessian comparison,
Proposition 6.33 and Lemma 6.40, pp. 120-121, 126-127. -/
theorem exponentialJacobi_index_eq_hessian
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2)
    (W : G.Horizontal x) :
    let Q := initialValuePath_differentialData hM04 hM12
      (exponentialInitialValuePath E Z s hs hpos) W
    (∫ r in 0..s, pullbackIndexPairDensity (E.square_path Z s hs hpos)
      Q.extension Q.extension r) =
      (2 * s) * M14ReducedLengthHessianPairing G
        ⟨(E.square_path Z s hs hpos).curve s, hq⟩ (M14ReducedLengthAt G T 0 x)
        (Q.field s) (Q.field s) := by
  let R := E.square_path Z s hs hpos
  let P := exponentialInitialValuePath E Z s hs hpos
  let Q := initialValuePath_differentialData hM04 hM12 P W
  let O := range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)
  obtain ⟨V, hmem, hV⟩ := exists_initialVectorVariation hM04 hM12 E Z W hs hpos
  obtain ⟨D⟩ := exists_variationDerivativeData V
  have hfield (r : ℝ) (hr : r ∈ M14SqrtParameterInterval 0 (s ^ 2)) :
      M14VariationField V r = Q.field r := by
    have hr' : r ∈ Icc 0 s := by
      simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using hr
    have hsurv := (E.maximal_lifetime Z).out (E.domain_zero Z) hs hr'
    exact eq_of_heq ((initialVectorVariation_field_at E Z W hs hpos V hV hr hsurv).trans
      (exponentialJacobiField_heq_differential hM04 hM12 E Z W hs hpos hr hsurv).symm)
  obtain ⟨H, hZH⟩ := jointDomain_stableSet E hz
  have hmin := exponentialPath_minimizing_of_uniqueBranch E hpos hs
    (stableInitialVector_unique_branch E ((H.carrier_exact Z).mp hZH))
  have hpoint' : R.curve (Real.sqrt (s ^ 2)) = E.gamma Z s := by
    rw [Real.sqrt_sq hpos.le]
    exact hpoint
  have hp : R.curve (Real.sqrt (s ^ 2)) ∈ O := hpoint'.symm ▸ ⟨⟨(Z, s), hz⟩, rfl⟩
  have hd : ∀ V : G.Horizontal (R.curve s),
      mvfderiv (spacetimeModel n) (M14ReducedLengthAt G T 0 x) (R.curve s) V.val =
        G.spacetime.horizontalMetric.inner (R.curve s) (R.horizontal_velocity s) V / (2 * s) :=
    horizontal_momentum_transport hpoint (M14ReducedLengthAt G T 0 x) (R.horizontal_velocity s)
      (2 * s) (reducedLengthAt_horizontal_differential hCoordinates hM04 hM12 E hs hpos hz hpoint)
  have hclock : G.spacetime.timeFunction (R.curve (Real.sqrt (s ^ 2))) = T - s ^ 2 := by
    rw [Real.sqrt_sq hpos.le]
    exact hq
  have ha := initialVectorVariation_action_germ E Z W hs hpos hz V hmem hV
  have hi := variation_index_eq_hessian_of_action_germ hCoordinates hM04 hM12 V D hmin
    (initialVectorVariation_initialFixed E Z W hs hpos V hV)
    (M14ReducedLengthAt G T 0 x) O (jointMap_range_isOpen E) hp
    (reducedLengthAt_contMDiffOn_jointImage hM04 hM12 E)
    (by simpa only [Real.sqrt_sq hpos.le] using ha)
    (by rw [Real.sqrt_sq hpos.le]; exact hd) hclock
  rw [secondVariationIndexForm_eq_of_field V D Q.extension hfield,
    hfield _ ⟨Real.sqrt_le_sqrt (sq_nonneg s), le_rfl⟩,
    hessian_pair_parameter_congr R.curve Q.field (M14ReducedLengthAt G T 0 x)
      (Real.sqrt_sq hpos.le) hclock hq, Real.sqrt_zero, Real.sqrt_sq hpos.le] at hi
  exact hi

/-- The terminal Jacobi boundary pair equals twice square time times
the raw endpoint Hessian. Its initial boundary contribution vanishes,
Lemma 6.19 and Lemma 6.40, pp. 114, 126-127. -/
theorem exponentialJacobi_boundary_eq_hessian
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2)
    (W : G.Horizontal x) :
    let Q := initialValuePath_differentialData hM04 hM12
      (exponentialInitialValuePath E Z s hs hpos) W
    G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve s)
      (M14JacobiFirstDerivative Q s) (Q.field s) =
      (2 * s) * M14ReducedLengthHessianPairing G
        ⟨(E.square_path Z s hs hpos).curve s, hq⟩ (M14ReducedLengthAt G T 0 x)
        (Q.field s) (Q.field s) := by
  let R := E.square_path Z s hs hpos
  let P := exponentialInitialValuePath E Z s hs hpos
  let Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval 0 (s ^ 2)) :=
    initialValuePath_differentialData hM04 hM12 P W
  have hzero : Q.field 0 = 0 := initialValuePath_differentialField_zero hM04 hM12 P W
  have hres : (∫ r in Real.sqrt 0..Real.sqrt (s ^ 2),
      M14JacobiResidual G R Q r (Q.field r)) = 0 := by
    calc
      _ = ∫ r in Real.sqrt 0..Real.sqrt (s ^ 2), (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt (sq_nonneg s))
          (fun r hr => initialValuePath_differential_jacobi hM04 hM12 P W
            (Ioo_subset_Icc_self hr) (Q.field r))
      _ = 0 := intervalIntegral.integral_zero
  have hg := integral_pullbackIndexPairDensity R Q Q.extension hM04 hM12
  rw [hres] at hg
  let F : ℝ → ℝ := pullbackIndexPairDensity R Q.extension Q.extension
  let B : ℝ → ℝ := pullbackIndexBoundaryPair R Q.extension Q.field
  change (∫ r in Real.sqrt 0..Real.sqrt (s ^ 2), F r) =
    B (Real.sqrt (s ^ 2)) - B (Real.sqrt 0) - 0 at hg
  rw [Real.sqrt_zero, Real.sqrt_sq hpos.le] at hg
  simp only [B, pullbackIndexBoundaryPair, hzero, sub_zero] at hg
  rw [(G.spacetime.horizontalMetric.inner (R.curve 0)
    (M14HorizontalCovariantDerivative G R.curve (M14SqrtParameterInterval 0 (s ^ 2))
      Q.field Q.extension 0)).map_zero, sub_zero] at hg
  exact hg.symm.trans (exponentialJacobi_index_eq_hessian hCoordinates hM04 hM12 E
    hs hpos hz hpoint hq W)

end PoincareMT.M14
