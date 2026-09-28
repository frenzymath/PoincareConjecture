import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Normalization
import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem exists_scalarCurvature_constant (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : M, (K.flow.connection t).scalarCurvature x = R := by
  obtain ⟨R, hR, hscalar⟩ :=
    (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp (C.sphere.round t ht)
  refine ⟨R, hR, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.scalarCurvature_cover ht p, hscalar]

theorem scalarCurvature_eq (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x y : M) :
    (K.flow.connection t).scalarCurvature x =
      (K.flow.connection t).scalarCurvature y := by
  obtain ⟨R, _, hR⟩ := C.exists_scalarCurvature_constant ht
  rw [hR x, hR y]

theorem scalarCurvature_pos (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    0 < (K.flow.connection t).scalarCurvature x := by
  obtain ⟨R, hR, hscalar⟩ := C.exists_scalarCurvature_constant ht
  rw [hscalar x]
  exact hR

theorem scalarCurvatureSupOn_eq (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) {X : Set M} (hX : X.Nonempty) (p : M) :
    scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t) X =
      (K.flow.connection t).scalarCurvature p := by
  obtain ⟨x, hx⟩ := hX
  let : Nonempty X := ⟨⟨x, hx⟩⟩
  have heq : (fun z : X => (K.flow.connection t).scalarCurvature z.1) =
      fun _ => (K.flow.connection t).scalarCurvature p :=
    funext fun z => C.scalarCurvature_eq ht z.1 p
  rw [scalarCurvatureSupOn, heq]
  simp

theorem scalarGradientNorm_eq_zero (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x = 0 := by
  obtain ⟨R, _, hR⟩ := C.exists_scalarCurvature_constant ht
  have heq : (K.flow.connection t).scalarCurvature = fun _ => R := funext hR
  unfold scalarGradientNorm
  rw [heq]
  simp only [mvfderiv_const]
  rcases isEmpty_or_nonempty
      {v : TangentSpace (𝓡 3) x // (K.flow.metric t).inner x v v = 1} with h | h
  · rw [Set.range_eq_empty_iff.mpr h]
    exact Real.sSup_empty
  · simp

theorem scalarLaplacian_eq_zero (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    (K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x = 0 := by
  obtain ⟨R, _, hR⟩ := C.exists_scalarCurvature_constant ht
  have heq : (K.flow.connection t).scalarCurvature = fun _ => R := funext hR
  rw [heq]
  simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
    LeviCivitaData.hessianOnFields, mvfderiv_const]

theorem scalarEvolution_bound (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    |(K.flow.connection t).laplacian (K.flow.connection t).scalarCurvature x +
      2 * (K.flow.connection t).ricciNormSq x| ≤
        2 * (K.flow.connection t).scalarCurvature x ^ 2 := by
  have hD := P.tensor_calculus 3 M (K.flow.metric t) (K.flow.connection t)
  have hRic : ∀ v : TangentSpace (𝓡 3) x,
      0 ≤ (K.flow.connection t).ricci x v v := fun v =>
    ((K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator hD x
      (K.nonnegative_curvature_operator t ht x) v).1
  have hnorm :=
    (K.flow.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg hD x hRic
  have hnorm0 : 0 ≤ (K.flow.connection t).ricciNormSq x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [C.scalarLaplacian_eq_zero ht x, zero_add,
    abs_of_nonneg (mul_nonneg (by norm_num) hnorm0)]
  linarith

theorem scalarDerivWithin_bound (C : M27TwistedSphereLineFlowCertificate K)
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {t : ℝ} (ht : t ≤ 0) (x : M) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x)
        d (Set.Iic 0) t ∧
      |d| ≤ 2 * (K.flow.connection t).scalarCurvature x ^ 2 := by
  exact ⟨_, P.scalar_evolution M (Set.Iic 0) K.flow t ht x,
    C.scalarEvolution_bound P ht x⟩

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
