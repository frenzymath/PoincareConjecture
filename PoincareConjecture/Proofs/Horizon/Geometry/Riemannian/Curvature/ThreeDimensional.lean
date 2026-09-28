import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.AlgebraicSpectrum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Definitions

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem three_dimensional_curvature_operator_spectrum
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ b : OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
    let W := fun u v : TangentSpace (𝓡 3) x =>
      (WithLp.toLp 2 (crossProduct (b.repr u) (b.repr v)) :
        EuclideanSpace ℝ (Fin 3))
    let T := Poincare.Geometry.Curvature.Operator.curvatureOperator
      (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l))
    T.IsSymmetric ∧
    (∀ u v w z, inner ℝ (W u v) (W w z) =
      g.inner x u w * g.inner x v z - g.inner x u z * g.inner x v w) ∧
    (∀ a : EuclideanSpace ℝ (Fin 3), ‖a‖ = 1 →
      ∃ u v, IsOrthonormalPair g x u v ∧ W u v = a) ∧
    (∀ u v w z, D.curvatureTensor x u v w z =
      inner ℝ (W u v) (T (W w z))) ∧
    ∃ k : Fin 3 → ℝ,
    ∃ e : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)),
      Antitone k ∧
      (∀ i, T (e i) = k i • e i) ∧
      D.leastSectionalCurvature x = k 2 ∧
      D.scalarCurvature x = 2 * (k 0 + k 1 + k 2) ∧
      D.curvatureTensorNorm x ^ 2 = 4 * (k 0 ^ 2 + k 1 ^ 2 + k 2 ^ 2) := by
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
  refine ⟨b,
    Poincare.Geometry.Curvature.Operator.curvatureOperator_isSymmetric _
      (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1),
    Poincare.Geometry.Curvature.Operator.crossProduct_repr_inner b, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨u, v, hu, hv, huv, hW⟩ :=
      Poincare.Geometry.Curvature.Operator.exists_orthonormal_crossProduct_repr b a ha
    exact ⟨u, v, ⟨hu, hv, huv⟩, hW⟩
  · intro u v w z
    simpa only [hA] using
      Poincare.Geometry.Curvature.Operator.multilinear_eq_curvatureOperator_pairing
        A b hfirst hlast u v w z
  have hscalar : (∑ i, ∑ j, A ![b i,b j,b i,b j]) = D.scalarCurvature x := by
    simp only [← hA, b, OrthonormalBasis.reindex_apply]
    simp only [← Equiv.sum_comp (finCongr hd).symm, LeviCivitaData.scalarCurvature,
      LeviCivitaData.ricci]
  have hnorm : (∑ i, ∑ j, ∑ k, ∑ l, (A ![b i,b j,b k,b l]) ^ 2) =
      D.curvatureTensorNorm x ^ 2 := by
    simp only [← hA, b, OrthonormalBasis.reindex_apply]
    rw [LeviCivitaData.curvatureTensorNorm, Real.sq_sqrt (by positivity)]
    simp only [← Equiv.sum_comp (finCongr hd).symm]
  obtain ⟨k, e, horder, heigen, hleast, htrace, henergy⟩ :=
    Poincare.Geometry.Curvature.Operator.algebraic_three_operator_spectrum A b hfirst hlast hpair
  refine ⟨k, e, horder, ?_, ?_, hscalar.symm.trans htrace,
    hnorm.symm.trans henergy⟩
  · simpa only [hA] using heigen
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
