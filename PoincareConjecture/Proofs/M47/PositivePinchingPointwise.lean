import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TensorCone
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.M04.SectionalRayleigh

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47Positive

open PoincareConjecture.AncientKappaRoundness
open Poincare.Geometry.Curvature.Operator
open PoincareConjecture.M04

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
  VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
    (TangentSpace (𝓡 3) : M → Type _) x

omit [T2Space M] in
private theorem exists_frame_of_unit (x : M) (v : TangentSpace (𝓡 3) x)
    (hv : g.inner x v v = 1) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x), b 0 = v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm : ‖v‖ = 1 := by
    have hsq : ‖v‖ ^ 2 = 1 := (real_inner_self_eq_norm_sq v).symm.trans hv
    nlinarith [norm_nonneg v]
  have hon : Orthonormal ℝ
      (({0} : Set (Fin 3)).domRestrict (fun _ : Fin 3 => v)) := by
    let : Subsingleton ↥({0} : Set (Fin 3)) := Set.subsingleton_singleton.coe_sort
    exact ⟨fun _ => hnorm, Subsingleton.pairwise⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := TangentSpace (𝓡 3) x) (ι := Fin 3)
    (v := fun _ => v) (s := {0}) (by simpa using hdim) hon
  exact ⟨b, hb 0 (mem_singleton 0)⟩

omit [T2Space M] in
private theorem complement_eq_inner (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let A := TensorFiber.operatorTensorEquiv.symm (D.ricciComplementTensor hD x)
    ∀ v w : TangentSpace (𝓡 3) x,
      D.ricciComplementEvaluation x ![v, w] = inner ℝ v (A w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  intro v w
  have h := congrArg (fun T : TensorFiber (TangentSpace (𝓡 3) x) 2 => T ![v, w])
    (TensorFiber.operatorTensorEquiv.apply_symm_apply (D.ricciComplementTensor hD x))
  simpa only [TensorFiber.operatorTensorEquiv_apply, TensorFiber.operatorTensor_apply,
    D.ricciComplementTensor_apply, ContinuousLinearMap.coe_coe] using h.symm

omit [T2Space M] in

theorem ricciComplement_mem_iff (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (c : ℝ) :
    (letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩;
      D.ricciComplementTensor hD x ∈ tensorPinchingCone c) ↔
    (∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
      0 ≤ D.ricciComplementEvaluation x ![v, v]) ∧
    ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v v = 1 → g.inner x w w = 1 →
      D.ricciComplementEvaluation x ![v, v] ≤
        c * D.ricciComplementEvaluation x ![w, w] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := TensorFiber.operatorTensorEquiv.symm (D.ricciComplementTensor hD x)
  have heval := complement_eq_inner D hD x
  have hunit (v : TangentSpace (𝓡 3) x) : g.inner x v v = 1 ↔ ‖v‖ = 1 := by
    change inner ℝ v v = 1 ↔ ‖v‖ = 1
    rw [real_inner_self_eq_norm_sq]
    constructor
    · intro h
      nlinarith [norm_nonneg v]
    · intro h
      rw [h]
      norm_num
  have hsym : A.toLinearMap.IsSymmetric := by
    intro v w
    simp only [ContinuousLinearMap.coe_coe]
    rw [real_inner_comm w (A v)]
    change inner ℝ w (A v) = inner ℝ v (A w)
    rw [← heval, ← heval, D.ricciComplementEvaluation_symm hD]
  change A.toLinearMap.IsSymmetric ∧ _ ↔ _
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v w hv hw => ?_⟩
    · rw [heval]
      exact h.2.1 v ((hunit v).mp hv)
    · rw [heval, heval]
      exact h.2.2 v w ((hunit v).mp hv) ((hunit w).mp hw)
  · rintro ⟨hnonneg, hratio⟩
    refine ⟨hsym, fun v hv => ?_, fun v w hv hw => ?_⟩
    · rw [← heval]
      exact hnonneg v ((hunit v).mpr hv)
    · rw [← heval, ← heval]
      exact hratio v w ((hunit v).mpr hv) ((hunit w).mpr hw)

theorem ricciComplement_lower_of_sectional_lower
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) (m : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 3) x,
      m * metricGram g x u v ≤ D.curvatureTensor x u v u v)
    (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
    m ≤ D.ricciComplementEvaluation x ![v, v] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨b, hb⟩ := exists_frame_of_unit x v hv
  have h := hsec (b 1) (b 2)
  have hgram : metricGram g x (b 1) (b 2) = 1 := by
    change inner ℝ (b 1) (b 1) * inner ℝ (b 2) (b 2) -
      (inner ℝ (b 1) (b 2)) ^ 2 = 1
    simp [b.inner_eq_ite]
  rw [hgram, mul_one] at h
  have heq := D.ricciComplementTensor_apply_orthonormalBasis hD x b 0 0
  rw [D.ricciComplementTensor_apply] at heq
  change D.ricciComplementEvaluation x ![b 0, b 0] =
    D.curvatureTensor x (b 1) (b 2) (b 1) (b 2) at heq
  rw [← heq] at h
  simpa only [hb] using h

omit [T2Space M] in

theorem ricciComplement_le_half_scalar
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v : TangentSpace (𝓡 3) x, 0 ≤ D.curvatureTensor x u v u v)
    (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
    D.ricciComplementEvaluation x ![v, v] ≤ D.scalarCurvature x / 2 := by
  have hRic : 0 ≤ D.ricci x v v :=
    Finset.sum_nonneg fun i _ => hsec v (g.orthonormalBasis x i)
  change D.scalarCurvature x / 2 * g.inner x v v - D.ricci x v v ≤ _
  rw [hv, mul_one]
  exact sub_le_self _ hRic

theorem ricci_lower_of_complement_pinching
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    {c : ℝ} (hc : 1 ≤ c)
    (hpinch : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      D.ricciComplementTensor hD x ∈ tensorPinchingCone c)
    (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
    D.scalarCurvature x / (c + 2) ≤ D.ricci x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨b, hb⟩ := exists_frame_of_unit x v hv
  let a : Fin 3 → ℝ := fun i => D.ricciComplementEvaluation x ![b i, b i]
  have hunit (i : Fin 3) : g.inner x (b i) (b i) = 1 := b.inner_eq_one i
  have hratio := ((ricciComplement_mem_iff D hD x c).mp hpinch).2
  have h01 : a 0 ≤ c * a 1 := hratio _ _ (hunit 0) (hunit 1)
  have h02 : a 0 ≤ c * a 2 := hratio _ _ (hunit 0) (hunit 2)
  have hscalar : D.scalarCurvature x = 2 * (a 0 + a 1 + a 2) := by
    have htrace := D.scalarCurvature_eq_twice_trace_curvatureOperator hD x b
    have heq (i : Fin 3) : a i = curvatureMatrix
        (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)) i i := by
      exact (D.ricciComplementTensor_apply hD x _).symm.trans
        (D.ricciComplementTensor_apply_orthonormalBasis hD x b i i)
    simpa only [curvatureOperator_trace, Matrix.trace, Matrix.diag_apply,
      Fin.sum_univ_three, ← heq] using htrace
  have hRic : D.ricci x v v = a 1 + a 2 := by
    have heval : a 0 = D.scalarCurvature x / 2 - D.ricci x v v := by
      change D.scalarCurvature x / 2 * g.inner x (b 0) (b 0) -
        D.ricci x (b 0) (b 0) = _
      rw [hb, hv, mul_one]
    linarith only [hscalar, heval]
  apply (div_le_iff₀ (by linarith : 0 < c + 2)).mpr
  rw [hscalar, hRic]
  nlinarith only [h01, h02]

end PoincareConjecture.M47Positive
