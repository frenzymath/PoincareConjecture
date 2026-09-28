import PoincareConjecture.Proofs.M14.Sec6_5_SquareScalarField
import PoincareConjecture.Proofs.M14.Sec6_5_RegularSpatialDerivative
import PoincareConjecture.Proofs.M14.Sec6_3_StrictPrefix

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem inner_transport {q r : G.Point} (h : q = r) (A : G.Horizontal q) :
    G.spacetime.horizontalMetric.inner r (h ▸ A) (h ▸ A) =
      G.spacetime.horizontalMetric.inner q A A := by
  cases h
  rfl

private theorem scalar_transport {q r : G.Point} (h : q = r)
    (f : G.Point → ℝ) (A : G.Horizontal q) :
    mvfderiv (spacetimeModel n) f q A.val =
      mvfderiv (spacetimeModel n) f r (h ▸ A).val := by
  cases h
  rfl

theorem reducedLengthAt_time_derivative_square
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s) :
    M14BackwardTimeDerivative G (M14ReducedLengthAt G T 0 x) (E.gamma Z s) =
      horizontalScalarCurvature G.leafwise (E.gamma Z s) / 2 -
        G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve s)
          ((E.square_path Z s hs hpos).horizontal_velocity s)
          ((E.square_path Z s hs hpos).horizontal_velocity s) / (8 * s ^ 2) -
        E.action Z s / (4 * s ^ 3) := by
  let R := E.square_path Z s hs hpos
  let C := M14SqrtParameterInterval 0 (s ^ 2)
  let f := M14ReducedLengthAt G T 0 x
  have hCeq : C = Icc 0 s := by
    change M14SqrtParameterInterval 0 (s ^ 2) = Icc 0 s
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le]
  have hsC : s ∈ C := hCeq ▸ (show s ∈ Icc 0 s from ⟨hpos.le, le_rfl⟩)
  have hC : UniqueDiffWithinAt ℝ C s := by
    rw [hCeq]
    exact uniqueDiffOn_Icc hpos s ⟨hpos.le, le_rfl⟩
  have hsurv : C ⊆ {r | (Z, r) ∈ E.domain} := by
    intro r hr
    exact (E.maximal_lifetime Z).out (E.domain_zero Z) hs (hCeq ▸ hr)
  obtain ⟨H, hZH⟩ := jointDomain_stableSet E hz
  have hprefix : ∀ r ∈ Ioc 0 s, (Z, r) ∈ M14JointDomain G E := by
    intro r hr
    rcases lt_or_eq_of_le hr.2 with hlt | rfl
    · apply mem_jointDomain_of_stable_extension hCoordinates hM04 hM12 E H hZH
      simpa only [Real.sqrt_sq hpos.le] using (show r ∈ Ioo 0 s from ⟨hr.1, hlt⟩)
    · exact hz
  have hnear : (fun r => f (R.curve r)) =ᶠ[𝓝[C] s] (fun r => E.action Z r / (2 * r)) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpos)]
      with r hr hr0
    have hrc : r ∈ Icc 0 s := hCeq ▸ hr
    exact (congrArg f (exponential_square_curve_eq E Z hs hpos hr)).trans
      (reducedLengthAt_jointEndpoint E (hprefix r ⟨hr0, hrc.2⟩))
  have hden : HasDerivWithinAt (fun r : ℝ => 2 * r) 2 C s := by
    simpa only [id_eq, mul_one] using (hasDerivWithinAt_id s C).const_mul 2
  have hquot := ((E.action_time_derivative Z s hs hpos).mono hsurv).div hden
    (mul_pos zero_lt_two hpos).ne'
  have hnorm := hquot.congr_of_eventuallyEq_of_mem hnear hsC
  have hq : E.gamma Z s ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) :=
    ⟨⟨(Z, s), hz⟩, rfl⟩
  have hfq := (((reducedLengthAt_contMDiffOn_jointImage hM04 hM12 E) _ hq).contMDiffAt
    ((jointMap_range_isOpen E).mem_nhds hq)).mdifferentiableAt (by simp)
  have hf : MDifferentiableAt (spacetimeModel n) (𝓘(ℝ, ℝ)) f (R.curve s) := by
    rw [show R.curve s = E.gamma Z s from hpoint]
    exact hfq
  have hsp := reducedLengthAt_horizontal_differential hCoordinates hM04 hM12 E hs hpos hz
    hpoint (hpoint ▸ R.horizontal_velocity s)
  rw [inner_transport hpoint] at hsp
  have hfield := (scalar_transport hpoint f (R.horizontal_velocity s)).trans hsp
  have hchain := squareRoot_scalarField_hasDerivWithinAt R hsC hf
  rw [hfield] at hchain
  have heq := (hchain.derivWithin hC).symm.trans (hnorm.derivWithin hC)
  have ht := congrArg (M14BackwardTimeDerivative G f) hpoint
  have hS := congrArg (horizontalScalarCurvature G.leafwise) hpoint
  rw [ht, hS] at heq
  change 2 * s * M14BackwardTimeDerivative G f (E.gamma Z s) +
      G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s) / (2 * s) =
    (((1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s) +
        2 * s ^ 2 * horizontalScalarCurvature G.leafwise (E.gamma Z s)) * (2 * s) -
      E.action Z s * 2) / (2 * s) ^ 2 at heq
  change M14BackwardTimeDerivative G f (E.gamma Z s) =
    horizontalScalarCurvature G.leafwise (E.gamma Z s) / 2 -
      G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s) / (8 * s ^ 2) -
      E.action Z s / (4 * s ^ 3)
  field_simp [hpos.ne'] at heq ⊢
  nlinarith [heq]

end PoincareConjecture.M14
