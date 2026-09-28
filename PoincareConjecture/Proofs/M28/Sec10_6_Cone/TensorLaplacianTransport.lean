import PoincareConjecture.Proofs.M28.Sec10_6_Cone.ConeAnnulusTransport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.LaplacianRegularity
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import PoincareConjecture.Proofs.M04.RicciRegularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M28

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

set_option maxHeartbeats 800000 in

theorem tensorLaplacian_eq_of_local_isometry
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
      g.inner y u v = h.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y u)
        (mfderiv (𝓡 3) (𝓡 3) f y v))
    {x : M} (hx : x ∈ U)
    (v : Fin 2 → TangentSpace (𝓡 3) x) :
    D.tensorLaplacian D.ricciEvaluation x v =
      D'.tensorLaplacian D'.ricciEvaluation (f x)
        (fun i => mfderiv (𝓡 3) (𝓡 3) f x (v i)) := by
  classical
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let A := mfderiv (𝓡 3) (𝓡 3) f x
  let e : TangentSpace (𝓡 3) x ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (f x) :=
    LinearEquiv.ofBijective A.toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x
        (fun a b => (hmetric x hx a b).symm))
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  have hRicci : IsSmoothCovariantTensor D.ricciEvaluation :=
    PoincareConjecture.M04.isSmoothCovariantTensor_ricciEvaluation D
  have hRicci' : IsSmoothCovariantTensor D'.ricciEvaluation :=
    PoincareConjecture.M04.isSmoothCovariantTensor_ricciEvaluation D'
  have hIter' : IsSmoothCovariantTensor
      (D'.iteratedCovariantTensorDerivative D'.ricciEvaluation 2) :=
    PoincareConjecture.M04.isSmoothCovariantTensor_covariantTensorDerivative D'
      (PoincareConjecture.M04.isSmoothCovariantTensor_covariantTensorDerivative D'
        hRicci')
  obtain ⟨L, hL⟩ := hIter'.1 (f x)
  let σ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective ![2, 3, 0, 1] (by decide)
  let C4 := L.domDomCongr σ
  let C := (C4.curryLeft (A (v 0))).curryLeft (A (v 1))
  have hC (p q : TangentSpace (𝓡 3) (f x)) :
      C ![p, q] =
        D'.iteratedCovariantTensorDerivative D'.ricciEvaluation 2
          (f x) ![p, q, A (v 0), A (v 1)] := by
    rw [hL]
    change L ((Fin.cons (A (v 0)) (Fin.cons (A (v 1)) ![p, q])) ∘ σ) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  have hST : ∀ y ∈ U, ∀ w,
      D.ricciEvaluation y w =
        D'.ricciEvaluation (f y)
          (fun i => mfderiv (𝓡 3) (𝓡 3) f y (w i)) := by
    intro y hy w
    exact D.ricci_eq_of_local_isometry D' hU hf hmetric hy (w 0) (w 1)
  have hIter := D.iteratedCovariantTensorDerivative_eq_pullback D'
    hU hf hinv hmetric hRicci hRicci' hST 2 hx
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
          ![g.orthonormalBasis x i, g.orthonormalBasis x i, v 0, v 1] =
        C ![e (g.orthonormalBasis x i), e (g.orthonormalBasis x i)] := by
    have hi := hIter
      (v := ![g.orthonormalBasis x i, g.orthonormalBasis x i, v 0, v 1])
    rw [hC]
    change D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
        ![g.orthonormalBasis x i, g.orthonormalBasis x i, v 0, v 1] =
      D'.iteratedCovariantTensorDerivative D'.ricciEvaluation 2 (f x)
        ![A (g.orthonormalBasis x i), A (g.orthonormalBasis x i),
          A (v 0), A (v 1)]
    calc
      _ = D'.iteratedCovariantTensorDerivative D'.ricciEvaluation 2 (f x)
          (fun j => A (![g.orthonormalBasis x i, g.orthonormalBasis x i,
            v 0, v 1] j)) := by simpa only [A] using hi
      _ = _ := by
        congr 1
        funext j
        fin_cases j <;> rfl
  have hsum := bilinear_sum_orthonormalBasis_eq
    (bilinearOfTwoTensor C) ((g.orthonormalBasis x).map e')
      (h.orthonormalBasis (f x))
  simp only [LeviCivitaData.tensorLaplacian]
  have hsource :
      (∑ i, D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
        (Fin.cons (g.orthonormalBasis x i)
          (Fin.cons (g.orthonormalBasis x i) v))) =
        ∑ i, C ![e (g.orthonormalBasis x i), e (g.orthonormalBasis x i)] := by
    apply Finset.sum_congr rfl
    intro i hi
    have hv : Fin.cons (g.orthonormalBasis x i)
          (Fin.cons (g.orthonormalBasis x i) v) =
        ![g.orthonormalBasis x i, g.orthonormalBasis x i, v 0, v 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hv]
    exact hterm i
  have htarget :
      (∑ i, D'.iteratedCovariantTensorDerivative D'.ricciEvaluation 2 (f x)
        (Fin.cons (h.orthonormalBasis (f x) i)
          (Fin.cons (h.orthonormalBasis (f x) i)
            (fun j => A (v j))))) =
        ∑ i, C ![h.orthonormalBasis (f x) i,
          h.orthonormalBasis (f x) i] := by
    apply Finset.sum_congr rfl
    intro i hi
    have hv : Fin.cons (h.orthonormalBasis (f x) i)
          (Fin.cons (h.orthonormalBasis (f x) i)
            (fun j => A (v j))) =
        ![h.orthonormalBasis (f x) i, h.orthonormalBasis (f x) i,
          A (v 0), A (v 1)] := by
      funext j
      fin_cases j <;> rfl
    rw [hv, ← hC]
  have hsum' :
      (∑ i, C ![e (g.orthonormalBasis x i), e (g.orthonormalBasis x i)]) =
        ∑ i, C ![h.orthonormalBasis (f x) i,
          h.orthonormalBasis (f x) i] := by
    simp only [bilinearOfTwoTensor_apply] at hsum
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro i hi
      rfl
  exact hsource.trans (hsum'.trans htarget.symm)

end PoincareConjecture.M28
