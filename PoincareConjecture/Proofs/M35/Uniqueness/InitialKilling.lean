import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Proofs.M03.Existence.IntrinsicLieMetricNative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

private theorem mdifferentiableAt_linear_field {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (B y)) x := by
  rw [mdifferentiableAt_totalSpace]
  exact ⟨mdifferentiableAt_id, by
    simpa using B.differentiableAt.mdifferentiableAt⟩

private theorem mdifferentiableAt_const_field {n : ℕ}
    (x v : EuclideanSpace ℝ (Fin n)) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) v) x := by
  rw [mdifferentiableAt_totalSpace]
  exact ⟨mdifferentiableAt_id, by simpa using mdifferentiableAt_const (c := v)⟩

set_option backward.isDefEq.respectTransparency false in

theorem metricLieDerivative_linear {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x u v : EuclideanSpace ℝ (Fin n)) :
    DeTurckNative.metricLieDerivative D (fun y => B y) x u v =
      fderiv ℝ (fun y => g.inner y u v) x (B x) +
        g.inner x (B u) v + g.inner x u (B v) := by
  have h := DeTurckNative.metricLieDerivative_on_fields D
    (fun y => B y) (fun _ => u) (fun _ => v)
    (mdifferentiableAt_linear_field B x)
    (mdifferentiableAt_const_field x u) (mdifferentiableAt_const_field x v)
  have hb (w : EuclideanSpace ℝ (Fin n)) :
      VectorField.mlieBracket (𝓡 n) (fun y => B y) (fun _ => w) x = -B w := by
    simp only [VectorField.mlieBracket,
      VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin, fderivWithin_univ, fderiv_const_apply,
      B.fderiv, zero_apply, zero_sub]
  rw [hb, hb] at h
  have hm : mvfderiv (𝓡 n) (fun y => g.inner y u v) x (B x) =
      fderiv ℝ (fun y => g.inner y u v) x (B x) := by
    rw [mvfderiv, mfderiv_eq_fderiv]
    rfl
  rw [hm] at h
  simpa only [map_neg, neg_apply, sub_neg_eq_add] using h

theorem standardRotation_mfderiv
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x =
      (Matrix.toEuclideanLin A.1).toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (Matrix.toEuclideanLin A.1) x = _
  exact (Matrix.toEuclideanLin A.1).toContinuousLinearMap.fderiv

theorem initial_rotation_path_killing
    (g₀ : StandardInitialMetric)
    (A : ℝ → Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hzero : A 0 = 1)
    (hvelocity : ∀ x : StandardCapSpace,
      HasDerivAt (fun s => standardRotation (A s) x) (B x) 0)
    (x u v : StandardCapSpace) :
    DeTurckNative.metricLieDerivative g₀.connection (fun y => B y) x u v = 0 := by
  have hrot (s : ℝ) :
      g₀.metric.inner (standardRotation (A s) x)
        (standardRotation (A s) u) (standardRotation (A s) v) =
      g₀.metric.inner x u v := by
    have h := g₀.rotation_invariant (A s) x u v
    rw [standardRotation_mfderiv] at h
    exact h
  have hpoint (z : StandardCapSpace) : standardRotation (A 0) z = z := by
    rw [hzero]
    change Matrix.toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℝ) z = z
    simp
  have hG := ((g₀.metric.contDiffAt_euclideanCoefficients x).differentiableAt
    (by simp)).hasFDerivAt
  have hG' : HasFDerivAt g₀.metric.euclideanCoefficients
      (fderiv ℝ g₀.metric.euclideanCoefficients x) (standardRotation (A 0) x) := by
    simpa only [hpoint] using hG
  have hg := hG'.comp_hasDerivAt 0 (hvelocity x)
  have hpair := (hg.clm_apply (hvelocity u)).clm_apply (hvelocity v)
  have hconst : HasDerivAt
      (fun s => g₀.metric.inner (standardRotation (A s) x)
        (standardRotation (A s) u) (standardRotation (A s) v)) 0 0 := by
    simpa only [hrot] using hasDerivAt_const 0 (g₀.metric.inner x u v)
  have hderiv := hpair.unique hconst
  have hderiv' :
      fderiv ℝ g₀.metric.euclideanCoefficients x (B x) u v +
        g₀.metric.inner x (B u) v + g₀.metric.inner x u (B v) = 0 := by
    simp only [Function.comp_apply, hpoint, add_apply] at hderiv
    exact hderiv
  rw [metricLieDerivative_linear]
  change fderiv ℝ (fun y => g₀.metric.inner y u v) x (B x) +
      g₀.metric.inner x (B u) v + g₀.metric.inner x u (B v) = 0
  have hscalar := (hG.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)
  change HasFDerivAt (fun y => g₀.metric.inner y u v) _ x at hscalar
  have hs : fderiv ℝ (fun y => g₀.metric.inner y u v) x (B x) =
      fderiv ℝ g₀.metric.euclideanCoefficients x (B x) u v := by
    simpa using congrArg (fun L => L (B x)) hscalar.fderiv
  rw [hs]
  exact hderiv'

end PoincareConjecture.M35.Uniqueness
