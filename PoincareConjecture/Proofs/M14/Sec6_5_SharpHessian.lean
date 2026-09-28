import PoincareConjecture.Proofs.M14.Sec6_5_SharpAdaptedPair
import PoincareConjecture.Proofs.M14.Sec6_5_SharpTensorBasis
import PoincareConjecture.Proofs.M14.Sec6_5_SharpTraceEquality










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem field_zero_parameter_congr {γ : ℝ → G.Point}
    (Y : ∀ r, G.Horizontal (γ r)) {r s : ℝ} (h : r = s) (hY : Y r = 0) : Y s = 0 := by
  subst s
  exact hY

private theorem hessian_pair_parameter_congr (γ : ℝ → G.Point)
    (Y : ∀ r, G.Horizontal (γ r)) (f : G.Point → ℝ) {r s T τ : ℝ} (h : r = s)
    (hr : G.spacetime.timeFunction (γ r) = T - τ)
    (hs : G.spacetime.timeFunction (γ s) = T - τ) :
    M14ReducedLengthHessianPairing G ⟨γ r, hr⟩ f (Y r) (Y r) =
      M14ReducedLengthHessianPairing G ⟨γ s, hs⟩ f (Y s) (Y s) := by
  subst s
  rfl




theorem reducedLengthHessian_joint_sharp
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2)
    (hequality : M14ReducedLengthLaplacian (τ₁ := 0) G x
        ⟨(E.square_path Z s hs hpos).curve s, hq⟩ =
      (n : ℝ) / (2 * s ^ 2) -
        horizontalScalarCurvature G.leafwise ((E.square_path Z s hs hpos).curve s) -
        M14GeneralizedKIntegral G (E.path Z s hs hpos)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((E.path Z s hs hpos).curve t)) / (2 * s ^ 2 * Real.sqrt (s ^ 2)))
    (v w : G.Horizontal ((E.square_path Z s hs hpos).curve s)) :
    horizontalRicci G.leafwise ((E.square_path Z s hs hpos).curve s) v w +
      M14ReducedLengthHessianPairing G ⟨(E.square_path Z s hs hpos).curve s, hq⟩
        (M14ReducedLengthAt G T 0 x) v w =
      G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve s) v w /
        (2 * s ^ 2) := by
  classical
  let R := E.square_path Z s hs hpos
  have hsqrt : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hpos.le
  have hqroot : G.spacetime.timeFunction (R.curve (Real.sqrt (s ^ 2))) = T - s ^ 2 := by
    simpa only [hsqrt] using hq
  let q : (G.slices (T - s ^ 2)).Point := ⟨R.curve (Real.sqrt (s ^ 2)), hqroot⟩
  have hqimage : q.val ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2) := by
    change R.curve (Real.sqrt (s ^ 2)) ∈ _
    rw [hsqrt, show R.curve s = E.gamma Z s from hpoint]
    exact ⟨⟨(Z, s), hz⟩, rfl⟩
  obtain ⟨B, hB, hBsym⟩ := reducedLengthHessianPairing_exists_symm_bilinear hM04 hM12 E q
    hqimage
  have hbound (W : ∀ r, G.Horizontal (R.curve r))
      (EW : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 (s ^ 2)) W)
      (hW : W (Real.sqrt 0) = 0) :
      (2 * Real.sqrt (s ^ 2)) * B (W (Real.sqrt (s ^ 2))) (W (Real.sqrt (s ^ 2))) ≤
        ∫ r in Real.sqrt 0..Real.sqrt (s ^ 2), pullbackIndexPairDensity R EW EW r := by
    rw [← hB]
    have h := reducedLengthHessian_joint_le_index hCoordinates hM04 hM12 E hs hpos hz
      hpoint hq EW (field_zero_parameter_congr W Real.sqrt_zero hW)
    have h' : (2 * s) * M14ReducedLengthHessianPairing G ⟨R.curve s, hq⟩
        (M14ReducedLengthAt G T 0 x) (W s) (W s) ≤
        ∫ r in 0..s, pullbackIndexPairDensity R EW EW r := by
      have hm := (le_div_iff₀ (mul_pos zero_lt_two hpos)).mp h
      nlinarith only [hm]
    rw [hessian_pair_parameter_congr R.curve W (M14ReducedLengthAt G T 0 x)
      hsqrt hqroot hq]
    simpa only [Real.sqrt_zero, hsqrt] using h'
  obtain ⟨P, hP, horth, hbasis⟩ := exists_horizontalUnitAdaptedFrame R hM04 hM12
  let EP := fun i => Classical.choose (hP i).equation
  let J := fun i => pullbackIndexPairDensity R (horizontalAdaptedExtension (EP i))
    (horizontalAdaptedExtension (EP i))
  have hdiag (i : Fin n) : (∫ r in Real.sqrt 0..Real.sqrt (s ^ 2), J i r) =
      (2 * Real.sqrt (s ^ 2)) * B (P i (Real.sqrt (s ^ 2))) (P i (Real.sqrt (s ^ 2))) := by
    rw [← hB]
    have h : (∫ r in 0..s, J i r) =
        (2 * s) * M14ReducedLengthHessianPairing G ⟨R.curve s, hq⟩
          (M14ReducedLengthAt G T 0 x) (P i s) (P i s) :=
      adaptedIndexIntegral_eq_hessian_of_laplacian_eq hCoordinates hM04 hM12 E hs hpos hz
        hpoint hq hequality P hP EP horth i
    rw [hessian_pair_parameter_congr R.curve (P i) (M14ReducedLengthAt G T 0 x)
      hsqrt hqroot hq]
    simpa only [Real.sqrt_zero, hsqrt] using h
  obtain ⟨b, hb⟩ := hbasis (Real.sqrt (s ^ 2))
    (right_mem_Icc.mpr (Real.sqrt_le_sqrt (E.path Z s hs hpos).tau_lt.le))
  have hpair (i j : Fin n) : horizontalRicci G.leafwise q.val (b i) (b j) + B (b i) (b j) =
      G.spacetime.horizontalMetric.inner q.val (b i) (b j) / (2 * s ^ 2) := by
    rw [hb i, hb j]
    exact adaptedHessianPair_eq_of_index_equality R hM04 hM12 B hBsym hbound
      (hP i) (EP i) (EP j) (hdiag i)
  have hall (u z : G.Horizontal q.val) : horizontalRicci G.leafwise q.val u z +
      M14ReducedLengthHessianPairing G q (M14ReducedLengthAt G T 0 x) u z =
        G.spacetime.horizontalMetric.inner q.val u z / (2 * s ^ 2) := by
    rw [hB]
    exact ricci_add_bilinear_eq_of_basis hM12 q.val B (2 * s ^ 2) b hpair u z
  have hqs : q = ⟨R.curve s, hq⟩ := Subtype.ext (congrArg R.curve hsqrt)
  rw [hqs] at hall
  exact hall v w

end PoincareConjecture.M14
