import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Parabolic
import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.AlgebraicSpectrum
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.Bilinear
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators
open Poincare.Geometry.Curvature.Operator Poincare.HamiltonIvey

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem curvature_skew_first (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (u v w z : TangentSpace (𝓡 3) x) :
    D.curvatureTensor x u v w z = -D.curvatureTensor x v u w z := by
  calc
    D.curvatureTensor x u v w z = D.curvatureTensor x w z u v :=
      (hD.2.2.2.1 x u v w z).2.1
    _ = -D.curvatureTensor x w z v u := (hD.2.2.2.1 x w z u v).1
    _ = -D.curvatureTensor x v u w z :=
      congrArg Neg.neg (hD.2.2.2.1 x w z v u).2.1

theorem leastSectionalCurvature_eq_operator_eigenvalue
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
    D.leastSectionalCurvature x =
      (curvatureOperator_isSymmetric
        (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l))
        (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1)).eigenvalues
          (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b
  obtain ⟨A, hA⟩ := hD.1.1 x
  have heq (u v w z : TangentSpace (𝓡 3) x) :
      A ![u, v, w, z] = D.curvatureTensor x u v w z := (hA ![u, v, w, z]).symm
  have hfirst : ∀ u v w z, A ![u, v, w, z] = -A ![v, u, w, z] := by
    simpa only [heq] using curvature_skew_first D hD x
  have hlast : ∀ u v w z, A ![u, v, w, z] = -A ![u, v, z, w] := by
    intro u v w z
    simpa only [heq] using (hD.2.2.2.1 x u v w z).1
  have hpair : ∀ u v w z, A ![u, v, w, z] = A ![w, z, u, v] := by
    intro u v w z
    simpa only [heq] using (hD.2.2.2.1 x u v w z).2.1
  have hinner (u v : TangentSpace (𝓡 3) x) : inner ℝ u v = g.inner x u v := rfl
  simpa only [heq, hinner, leastSectionalCurvature, IsOrthonormalPair, and_assoc] using
    sectional_inf_eq_least_eigenvalue A b hfirst hlast hpair

theorem scalarCurvature_eq_twice_trace_curvatureOperator [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
    D.scalarCurvature x =
      2 * LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3))
        (curvatureOperator (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b
  have hswap (u v : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x u v u v = D.curvatureTensor x v u v u := by
    rw [curvature_skew_first D hD x, (hD.2.2.2.1 x v u u v).1, neg_neg]
  rw [← curvatureOperator_scalar_identity _
    (fun i j k l => curvature_skew_first D hD x (b i) (b j) (b k) (b l))
    (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).1)]
  let c := g.orthonormalBasis x
  have htrace (v : TangentSpace (𝓡 3) x) :
      (∑ i, D.curvatureTensor x (b i) v (b i) v) =
        ∑ j, D.curvatureTensor x (c j) v (c j) v :=
    bilinear_sum_orthonormalBasis_eq (D.curvatureTensor_bilinear_first_third x v v) b c
  change (∑ i, ∑ j, D.curvatureTensor x (c i) (c j) (c i) (c j)) = _
  symm
  rw [Finset.sum_comm]
  simp_rw [htrace]
  rw [Finset.sum_comm]
  simp_rw [hswap, htrace]
  exact Finset.sum_comm

theorem curvatureOperator_mem_region_iff [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) (t : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
    curvatureOperator (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)) ∈
        region (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) t ↔
      (D.scalarCurvature x / 2, D.negativeCurvaturePart x) ∈ scalarRegion t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b
  let R := fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hsymm := curvatureOperator_isSymmetric R
    (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1)
  have htrace : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (curvatureOperator R) =
      D.scalarCurvature x / 2 := by
    linarith [scalarCurvature_eq_twice_trace_curvatureOperator D hD x b]
  dsimp only [R] at htrace
  have hleast := leastSectionalCurvature_eq_operator_eigenvalue D hD x b
  constructor
  · rintro ⟨h, hm⟩
    simpa only [htrace, ← hleast, negativeCurvaturePart] using hm
  · intro hm
    refine ⟨hsymm, ?_⟩
    simpa only [htrace, ← hleast, negativeCurvaturePart] using hm

theorem scaled_curvatureOperator_mem_region_of_pinching [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    {a : ℝ} (ha : 0 ≤ a)
    (htrace : -6 / (1 + 4 * a) ≤ D.scalarCurvature x)
    (hlog : 0 < D.negativeCurvaturePart x →
      2 * D.negativeCurvaturePart x *
        (Real.log (D.negativeCurvaturePart x) + Real.log (1 + a) - 3) ≤
          D.scalarCurvature x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
      (1 + a) • curvatureOperator
          (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)) ∈
        region (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b
  apply (region_scale_iff _ ha _).mp
  apply (curvatureOperator_mem_region_iff D hD x a b).mpr
  apply PoincareConjecture.initial_scalar_region_of_pinching ha
  · nlinarith [htrace]
  · intro hX
    nlinarith [hlog hX]

theorem logarithmic_pinching_of_scaled_curvatureOperator_mem [T2Space M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    {t : ℝ} (ht : 0 ≤ t) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
      (1 + t) • curvatureOperator
          (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)) ∈
        region (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) 0 →
      0 < D.negativeCurvaturePart x →
        2 * D.negativeCurvaturePart x *
          (Real.log (D.negativeCurvaturePart x) + Real.log (1 + t) - 3) ≤
            D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro b hscaled
  have hmem := (region_scale_iff _ ht _).mpr hscaled
  have hsymm := curvatureOperator_isSymmetric
    (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l))
    (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1)
  have h := logarithmic_pinching_of_mem_region _ ht hsymm hmem
  have hleast := leastSectionalCurvature_eq_operator_eigenvalue D hD x b
  have hscalar := scalarCurvature_eq_twice_trace_curvatureOperator D hD x b
  dsimp only at h
  simpa only [← hleast, ← hscalar, negativeCurvaturePart] using h

end PoincareConjecture.LeviCivitaData
