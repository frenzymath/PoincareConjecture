import PoincareConjecture.Proofs.M14.Sec6_5_VariationContact
import PoincareConjecture.Proofs.M14.Sec6_5_PositiveStartDifferential

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

theorem sliceMinimum_variationAction_isLocalMin
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {B : ℝ}
    (hB : M14BackwardLAction G p < B)
    (hmin : ∀ (z : G.Point) (q : M14BackwardPath G T a b x z),
      M14BackwardLAction G q < B → M14BackwardLAction G p ≤ M14BackwardLAction G q)
    (V : M14LVariationData G p R) (hfix : V.left_endpoint_fixed) :
    IsLocalMin (M14VariationAction V) 0 := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hcont := (M14.variationAction_contDiffOn hM12 V).continuousOn.continuousAt
    (hP.mem_nhds hzero)
  have hnear : ∀ᶠ v in 𝓝 (0 : ℝ), M14VariationAction V v < B := by
    apply hcont.eventually (gt_mem_nhds _)
    simpa only [M14.variationAction_zero] using hB
  filter_upwards [hP.mem_nhds hzero, hnear] with v hv hbudget
  obtain ⟨q, hq⟩ := M14.exists_initialFixed_variationEndpointPath hM12 V hfix hv
  change M14VariationAction V 0 ≤ M14VariationAction V v
  rw [M14.variationAction_zero, ← hq]
  exact hmin _ q (hq ▸ hbudget)

theorem sliceMinimum_terminal_pair_eq_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {B : ℝ}
    (hB : M14BackwardLAction G p < B) (hp : M14IsMinimizing p)
    (hmin : ∀ (z : G.Point) (q : M14BackwardPath G T a b x z),
      M14BackwardLAction G q < B → M14BackwardLAction G p ≤ M14BackwardLAction G q)
    (W : G.Horizontal (R.curve (Real.sqrt b))) :
    G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
      (R.horizontal_velocity (Real.sqrt b)) W = 0 := by
  obtain ⟨V, hfix, hleft, hright⟩ :=
    M14.positiveStart_exists_terminalVariation hM12 W
  obtain ⟨E⟩ := M14.exists_squareRoot_velocity_extension R
  have hfirst := M14.firstVariation_euler_fixedInitial hCoordinates hM12 E
    (fun _ ht Z => M14.squareRootEulerResidual_eq_zero_of_minimizing
      hCoordinates hM12 hp E ht Z) V hleft
  rw [hright] at hfirst
  exact (sliceMinimum_variationAction_isLocalMin hM12 hB hmin V hfix).hasDerivAt_eq_zero
    hfirst

theorem sliceMinimum_terminal_velocity_eq_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {B : ℝ}
    (hB : M14BackwardLAction G p < B) (hp : M14IsMinimizing p)
    (hmin : ∀ (z : G.Point) (q : M14BackwardPath G T a b x z),
      M14BackwardLAction G q < B → M14BackwardLAction G p ≤ M14BackwardLAction G q) :
    R.horizontal_velocity (Real.sqrt b) = 0 := by
  by_contra hne
  have hpos := G.spacetime.horizontalMetric.pos (R.curve (Real.sqrt b))
    (R.horizontal_velocity (Real.sqrt b)) hne
  exact (ne_of_gt hpos) (sliceMinimum_terminal_pair_eq_zero hCoordinates hM12 hB hp hmin _)

end PoincareConjecture.Proofs.M46
