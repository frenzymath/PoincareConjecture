import PoincareConjecture.Proofs.M14.Sec6_5_RegularStableEndpoint
import PoincareConjecture.Proofs.M14.Sec6_5_DeltaAlgebra
import PoincareConjecture.Proofs.M14.Sec6_5_SharpHessian











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem sharp_tensor_slice_transport {T τ : ℝ} (f : G.Point → ℝ)
    (q r : (G.slices (T - τ)).Point) (h : q = r)
    (hr : ∀ v w : G.Horizontal r.val,
      horizontalRicci G.leafwise r.val v w + M14ReducedLengthHessianPairing G r f v w =
        G.spacetime.horizontalMetric.inner r.val v w / (2 * τ)) :
    ∀ v w : G.Horizontal q.val,
      horizontalRicci G.leafwise q.val v w + M14ReducedLengthHessianPairing G q f v w =
        G.spacetime.horizontalMetric.inner q.val v w / (2 * τ) := by
  subst q
  exact hr

private theorem sharp_tensor_endpoint_transport {T τ : ℝ} (f : G.Point → ℝ)
    (q : (G.slices (T - τ)).Point) (y : G.Point) (h : q.val = y)
    (hq : ∀ v w : G.Horizontal q.val,
      horizontalRicci G.leafwise q.val v w + M14ReducedLengthHessianPairing G q f v w =
        G.spacetime.horizontalMetric.inner q.val v w / (2 * τ)) :
    ∀ v w : G.Horizontal y,
      horizontalRicci G.leafwise y v w +
        M14ReducedLengthHessianPairing G q f (h.symm ▸ v) (h.symm ▸ w) =
          G.spacetime.horizontalMetric.inner y v w / (2 * τ) := by
  subst y
  exact hq




theorem regularFormulaData_nonempty
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (hz : (Z, s) ∈ M14JointDomain G E)
    (H : M14StableSet G T (s ^ 2) x E) (hZ : Z ∈ H.carrier) :
    Nonempty (M14RegularFormulaData G T (s ^ 2) x E H Z
      (regularStablePath E hs hpos H hZ)) := by
  let p := regularStablePath E hs hpos H hZ
  let O := range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)
  let dR := fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
    (p.curve t)
  obtain ⟨b, hb⟩ := exists_orthonormal_horizontalBasis G (H.endpoint_map Z)
  have hy : H.endpoint_map Z ∈ O := by
    rw [stableEndpoint_eq_exponential E hpos H hZ]
    exact ⟨⟨(Z, s), hz⟩, rfl⟩
  have hspace := reducedLengthAt_slice_contMDiffAt hM04 hM12 E (H.endpoint_slice_map Z)
    (by rw [H.endpoint_slice_map_val Z hZ]; exact hy)
  have htime := reducedLengthAt_stable_joint_time_identity E hs hpos H hZ
    hCoordinates hM04 hM12 hz
  have hgrad := reducedLengthGradientNormSq_stable_joint_identity E hs hpos H hZ
    hCoordinates hM04 hM12 hz b hb
  have hlap := reducedLengthLaplacian_stable_joint_bound E hs hpos H hZ
    hCoordinates hM04 hM12 hz
  let delta := (n : ℝ) / (2 * s ^ 2) -
    horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
    M14GeneralizedKIntegral G p dR / (2 * s ^ 2 * Real.sqrt (s ^ 2)) -
    M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z)
  have hd := reducedLength_delta_identities (sq_pos_of_pos hpos) (n : ℝ)
    (M14ReducedLengthValue G T 0 (s ^ 2) x (H.endpoint_map Z))
    (horizontalScalarCurvature G.leafwise (H.endpoint_map Z))
    (M14GeneralizedKIntegral G p dR)
    (M14BackwardTimeDerivative G (M14ReducedLengthAt G T 0 x) (H.endpoint_map Z))
    (M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z))
    (M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x (H.endpoint_map Z) b)
    htime hgrad
  refine ⟨{
    tau_pos := sq_pos_of_pos hpos
    carrier_mem := hZ
    path_minimizing := regularStablePath_minimizing E hs hpos H hZ
    path_endpoint := p.curve_end
    gradient_basis := b
    gradient_basis_orthonormal := hb
    regular_neighborhood := O
    regular_neighborhood_open := jointMap_range_isOpen E
    regular_center_mem := hy
    regular_representative := M14ReducedLengthAt G T 0 x
    regular_representative_eq := fun _ _ => rfl
    regular_spacetime_smooth := reducedLengthAt_contMDiffOn_jointImage hM04 hM12 E
    regular_space_smooth := hspace
    scalar_time_derivative := dR
    scalar_time_derivative_spec := fun _ _ => rfl
    kplain_integrable := exponential_weightedHarnack_intervalIntegrable hM12 E hs hpos
    reduced_length_time_derivative := rfl
    delta := delta
    delta_spec := rfl
    delta_nonnegative := sub_nonneg.mpr hlap
    partial_tau_identity := htime
    gradient_identity := hgrad
    laplacian_bound := hlap
    first_delta_identity := hd.1
    second_delta_identity := hd.2.1
    third_delta_identity := hd.2.2
    sharp_hessian_identity := ?_ }⟩
  intro hequality
  have hp := regular_square_endpoint E hs hpos
  have hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2 := by
    rw [hp]
    exact E.clock Z s hs
  have hslice := regularStable_slicePoint_eq E hs hpos H hZ hq
  have hscalar : horizontalScalarCurvature G.leafwise (H.endpoint_map Z) =
      horizontalScalarCurvature G.leafwise ((E.square_path Z s hs hpos).curve s) :=
    congrArg (horizontalScalarCurvature G.leafwise)
      ((stableEndpoint_eq_exponential E hpos H hZ).trans hp.symm)
  change M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z) =
    (n : ℝ) / (2 * s ^ 2) - horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
      M14GeneralizedKIntegral G (regularStablePath E hs hpos H hZ)
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          ((regularStablePath E hs hpos H hZ).curve t)) /
        (2 * s ^ 2 * Real.sqrt (s ^ 2)) at hequality
  rw [regularStablePath_actualK_eq, hslice, hscalar] at hequality
  apply sharp_tensor_endpoint_transport (M14ReducedLengthAt G T 0 x)
    (H.endpoint_slice_map Z) (H.endpoint_map Z) (H.endpoint_slice_map_val Z hZ)
  apply sharp_tensor_slice_transport (M14ReducedLengthAt G T 0 x)
    (H.endpoint_slice_map Z) ⟨(E.square_path Z s hs hpos).curve s, hq⟩ hslice
  exact reducedLengthHessian_joint_sharp hCoordinates hM04 hM12 E hs hpos hz hp hq hequality




theorem regularFormulaStatement
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) : M14RegularFormulaStatement G := by
  intro T x E z hz
  rcases z with ⟨Z, s⟩
  have hs := jointDomain_subset_domain E hz
  have hpos := jointDomain_time_pos E hz
  obtain ⟨H, hZ⟩ := jointDomain_stableSet E hz
  exact ⟨s ^ 2, H, sq_pos_of_pos hpos, hZ, (Real.sqrt_sq hpos.le).symm,
    regularStablePath E hs hpos H hZ, regularStablePath_minimizing E hs hpos H hZ,
    regularFormulaData_nonempty hCoordinates hM04 hM12 E hs hpos hz H hZ⟩

end PoincareConjecture.M14
