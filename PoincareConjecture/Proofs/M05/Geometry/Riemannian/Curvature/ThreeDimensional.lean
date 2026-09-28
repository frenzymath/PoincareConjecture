import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.AlgebraicSpectrum
import PoincareConjecture.Statements.Ch01.CurvatureCalculus
import PoincareConjecture.Definitions.Ch04.Pinching

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem three_dimensional_curvature_spectrum
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    ∃ k₁ k₂ k₃ : ℝ,
      k₁ ≥ k₂ ∧ k₂ ≥ k₃ ∧
      D.leastSectionalCurvature x = k₃ ∧
      D.scalarCurvature x = 2 * (k₁ + k₂ + k₃) ∧
      D.curvatureTensorNorm x ^ 2 = 4 * (k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let b := (g.orthonormalBasis x).reindex (finCongr hd)
  obtain ⟨A, hA'⟩ := hD.1.1 x
  have hA (u v w z : TangentSpace (𝓡 3) x) :
      D.curvatureTensor x u v w z = A ![u,v,w,z] := hA' ![u,v,w,z]
  have hfirst (u v w z : TangentSpace (𝓡 3) x) :
      A ![u,v,w,z] = -A ![v,u,w,z] := by
    simp only [← hA]
    calc
      D.curvatureTensor x u v w z = D.curvatureTensor x w z u v :=
        (hD.2.2.2.1 x u v w z).2.1
      _ = -D.curvatureTensor x w z v u := (hD.2.2.2.1 x w z u v).1
      _ = -D.curvatureTensor x v u w z := congrArg Neg.neg (hD.2.2.2.1 x w z v u).2.1
  have hlast (u v w z : TangentSpace (𝓡 3) x) :
      A ![u,v,w,z] = -A ![u,v,z,w] := by
    simpa only [← hA] using (hD.2.2.2.1 x u v w z).1
  have hpair (u v w z : TangentSpace (𝓡 3) x) :
      A ![u,v,w,z] = A ![w,z,u,v] := by
    simpa only [← hA] using (hD.2.2.2.1 x u v w z).2.1
  have hscalar : (∑ i, ∑ j, A ![b i,b j,b i,b j]) = D.scalarCurvature x := by
    simp only [← hA, b, OrthonormalBasis.reindex_apply]
    simp only [← Equiv.sum_comp (finCongr hd).symm, LeviCivitaData.scalarCurvature,
      LeviCivitaData.ricci]
  have hnorm : (∑ i, ∑ j, ∑ k, ∑ l, (A ![b i,b j,b k,b l]) ^ 2) =
      D.curvatureTensorNorm x ^ 2 := by
    simp only [← hA, b, OrthonormalBasis.reindex_apply]
    rw [LeviCivitaData.curvatureTensorNorm, Real.sq_sqrt (by positivity)]
    simp only [← Equiv.sum_comp (finCongr hd).symm]
  obtain ⟨k₁, k₂, k₃, h12, h23, hleast, htrace, henergy⟩ :=
    Poincare.Geometry.Curvature.Operator.algebraic_three_spectrum A b hfirst hlast hpair
  refine ⟨k₁, k₂, k₃, h12, h23, ?_, hscalar.symm.trans htrace,
    hnorm.symm.trans henergy⟩
  have hsection :
      {q : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
        inner ℝ u u = 1 ∧ inner ℝ v v = 1 ∧ inner ℝ u v = 0 ∧
          q = A ![u,v,u,v]} =
      {q : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
        IsOrthonormalPair g x u v ∧ q = D.curvatureTensor x u v u v} := by
    ext q
    constructor
    · rintro ⟨u, v, hu, hv, huv, hq⟩
      exact ⟨u, v, ⟨hu, hv, huv⟩, hq.trans (hA u v u v).symm⟩
    · rintro ⟨u, v, ⟨hu, hv, huv⟩, hq⟩
      exact ⟨u, v, hu, hv, huv, hq.trans (hA u v u v)⟩
  simpa only [hsection, leastSectionalCurvature] using hleast

end PoincareConjecture.LeviCivitaData
