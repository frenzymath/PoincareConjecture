import PoincareConjecture.Proofs.M09.BilinearTrace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff RealInnerProductSpace

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem mvfderiv_const_clm
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (f : M → V) (p : M)
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, V)) f p) (X : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ L (f q)) p X = L (mvfderiv (𝓡 n) f p X) := by
  have h := L.hasMFDerivAt.comp p hf.hasMFDerivAt
  convert! congrArg (fun A : TangentSpace (𝓡 n) p →L[ℝ] W ↦ A X) h.mfderiv using 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem inverseMetricTrace_mvfderiv
    (A B : M → E →L[ℝ] E) (p : M) (X : TangentSpace (𝓡 n) p)
    (hA : MDifferentiableAt (𝓡 n) (𝓘(ℝ, E →L[ℝ] E)) A p)
    (hB : MDifferentiableAt (𝓡 n) (𝓘(ℝ, E →L[ℝ] E)) B p)
    (hunit : IsUnit (A p)) (P Q C : E →L[ℝ] E)
    (hA' : mvfderiv (𝓡 n) A p X = A p * P + Q * A p)
    (hB' : mvfderiv (𝓡 n) B p X = B p * P + Q * B p + C) :
    mvfderiv (𝓡 n) (fun q ↦ continuousTrace (Ring.inverse (A q) * B q)) p X =
      continuousTrace (Ring.inverse (A p) * C) := by
  obtain ⟨a, ha⟩ := hunit
  have hinv : HasMFDerivAt (𝓡 n) (𝓘(ℝ, E →L[ℝ] E))
      (fun q ↦ Ring.inverse (A q)) p
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑a⁻¹ ↑a⁻¹).comp
        (mvfderiv (𝓡 n) A p)) := by
    have hout := hasFDerivAt_ringInverse (𝕜 := ℝ) a
    rw [ha] at hout
    convert! hout.hasMFDerivAt.comp p hA.hasMFDerivAt using 1
  have hprod := hinv.mul' hB.hasMFDerivAt
  have htrace := (continuousTrace (E := E)).hasMFDerivAt.comp p hprod
  have hder : mvfderiv (𝓡 n)
      (fun q ↦ continuousTrace (Ring.inverse (A q) * B q)) p X =
      continuousTrace (Ring.inverse (A p) * mvfderiv (𝓡 n) B p X +
        (-((↑a⁻¹ : E →L[ℝ] E) * mvfderiv (𝓡 n) A p X * (↑a⁻¹ : E →L[ℝ] E))) * B p) := by
    convert! congrArg (fun L : TangentSpace (𝓡 n) p →L[ℝ] ℝ ↦ L X) htrace.mfderiv using 1
  have hinvt : Ring.inverse (A p) = (↑a⁻¹ : E →L[ℝ] E) := by
    rw [← ha, Ring.inverse_unit]
  have halgebra : Ring.inverse (A p) * mvfderiv (𝓡 n) B p X +
      (-((↑a⁻¹ : E →L[ℝ] E) * mvfderiv (𝓡 n) A p X * (↑a⁻¹ : E →L[ℝ] E))) * B p =
      (↑a⁻¹ : E →L[ℝ] E) * C + ((↑a⁻¹ : E →L[ℝ] E) * B p) * P -
        P * ((↑a⁻¹ : E →L[ℝ] E) * B p) := by
    rw [hA', hB', hinvt, ← ha]
    noncomm_ring [a.inv_mul, a.mul_inv]
    simp only [← mul_assoc, a.inv_mul, one_mul]
  rw [hder, halgebra, map_sub, map_add, continuousTrace_mul_comm P,
    add_sub_cancel_right, hinvt]

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem metricFormTrace_contDiffAt (G B : V →L[ℝ] V →L[ℝ] ℝ)
    (hunit : IsUnit (formOperator G)) :
    ContDiffAt ℝ ∞ (fun z : (V →L[ℝ] V →L[ℝ] ℝ) × (V →L[ℝ] V →L[ℝ] ℝ) ↦
      metricFormTrace z.1 z.2) (G, B) := by
  have hG : ContDiffAt ℝ ∞ (fun z : (V →L[ℝ] V →L[ℝ] ℝ) ×
      (V →L[ℝ] V →L[ℝ] ℝ) ↦ formOperator z.1) (G, B) := by
    exact ((formOperator (E := V)).contDiff.comp contDiff_fst).contDiffAt
  have hB : ContDiffAt ℝ ∞ (fun z : (V →L[ℝ] V →L[ℝ] ℝ) ×
      (V →L[ℝ] V →L[ℝ] ℝ) ↦ formOperator z.2) (G, B) := by
    exact ((formOperator (E := V)).contDiff.comp contDiff_snd).contDiffAt
  obtain ⟨a, ha⟩ := hunit
  have hinv := contDiffAt_ringInverse (n := ∞) ℝ a
  rw [ha] at hinv
  exact continuousTrace.contDiff.contDiffAt.comp (G, B) ((hinv.comp (G, B) hG).mul hB)

theorem metricFormTrace_mvfderiv
    (G B : M → V →L[ℝ] V →L[ℝ] ℝ) (p : M) (X : TangentSpace (𝓡 n) p)
    (hG : MDifferentiableAt (𝓡 n) (𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) G p)
    (hB : MDifferentiableAt (𝓡 n) (𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) B p)
    (hunit : IsUnit (formOperator (G p))) (P : V →L[ℝ] V)
    (C : V →L[ℝ] V →L[ℝ] ℝ)
    (hG' : ∀ v w, mvfderiv (𝓡 n) G p X v w = G p (P v) w + G p v (P w))
    (hB' : ∀ v w, mvfderiv (𝓡 n) B p X v w = B p (P v) w + B p v (P w) + C v w) :
    mvfderiv (𝓡 n) (fun q ↦ metricFormTrace (G q) (B q)) p X =
      metricFormTrace (G p) C := by
  have hGO := (formOperator (E := V)).mdifferentiableAt.comp p hG
  have hBO := (formOperator (E := V)).mdifferentiableAt.comp p hB
  apply inverseMetricTrace_mvfderiv _ _ p X hGO hBO hunit P P.adjoint (formOperator C)
  · change mvfderiv (𝓡 n) (fun q ↦ formOperator (G q)) p X = _
    rw [mvfderiv_const_clm formOperator G p hG X]
    ext v
    apply ext_inner_right ℝ
    intro w
    simpa only [Function.comp_apply, add_apply, mul_apply_eq_comp, inner_add_left,
      ContinuousLinearMap.adjoint_inner_left, formOperator_pairing] using hG' v w
  · change mvfderiv (𝓡 n) (fun q ↦ formOperator (B q)) p X = _
    rw [mvfderiv_const_clm formOperator B p hB X]
    ext v
    apply ext_inner_right ℝ
    intro w
    simpa only [Function.comp_apply, add_apply, mul_apply_eq_comp, inner_add_left,
      ContinuousLinearMap.adjoint_inner_left, formOperator_pairing] using hB' v w

end InnerProduct

end PoincareConjecture.Proofs.M09
