import PoincareConjecture.Proofs.M09.FrameForms

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

noncomputable def curvatureSliceBilinear (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (q : M)
    (v w : TangentSpace (𝓡 n) q) :
    TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) q) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) q
  exact bilinearOfMultilinear (((hR.1 q).choose.curryLeft v).curryMid 1 w)

theorem curvatureSliceBilinear_apply (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (q : M)
    (v w a b : TangentSpace (𝓡 n) q) :
    curvatureSliceBilinear D hR q v w a b = D.curvatureTensor q v a w b := by
  simp only [curvatureSliceBilinear, bilinearOfMultilinear_apply]
  change (hR.1 q).choose (Fin.cons v ((1 : Fin 3).insertNth w ![a, b])) = _
  rw [← (hR.1 q).choose_spec]
  rfl

noncomputable def frameCurvatureSlice (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (p : M)
    (v w : TangentSpace (𝓡 n) p) (q : M) :
    TangentSpace (𝓡 n) p →L[ℝ] TangentSpace (𝓡 n) p →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (curvatureSliceBilinear D hR q (extensionMap p q v) (extensionMap p q w)).bilinearComp
    (extensionMap p q) (extensionMap p q)

theorem frameCurvatureSlice_apply (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (p : M)
    (v w : TangentSpace (𝓡 n) p) (q : M) (a b : TangentSpace (𝓡 n) p) :
    frameCurvatureSlice D hR p v w q a b =
      D.curvatureTensor q (extensionMap p q v) (extensionMap p q a)
        (extensionMap p q w) (extensionMap p q b) :=
  curvatureSliceBilinear_apply D hR q _ _ _ _

theorem frameCurvatureSlice_self (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (p : M)
    (v w : TangentSpace (𝓡 n) p) :
    frameCurvatureSlice D hR p v w p = curvatureSliceBilinear D hR p v w := by
  ext a b
  simp only [frameCurvatureSlice_apply, curvatureSliceBilinear_apply, extensionMap_self,
    ContinuousLinearMap.id_apply]

theorem frameCurvatureSlice_smooth (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (p : M)
    (v w : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ContMDiffOn (𝓡 n) (𝓘(ℝ, TangentSpace (𝓡 n) p →L[ℝ]
      TangentSpace (𝓡 n) p →L[ℝ] ℝ)) ∞ (frameCurvatureSlice D hR p v w)
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  apply contMDiffOn_bilinear_iff.mpr
  intro a b
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have h := hR.2 e.baseSet e.open_baseSet
    (fun i q ↦ extensionMap p q (![v, a, w, b] i)) (fun i ↦ extensionMap_smooth p _)
  simpa [frameCurvatureSlice_apply, LeviCivitaData.riemannEvaluation, e] using h

theorem frameCurvatureSlice_derivative (D : LeviCivitaData g)
    (hR : IsSmoothCovariantTensor D.riemannEvaluation) (p : M)
    (X v w a b : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q ↦ frameCurvatureSlice D hR p v w q a b) p X =
      D.covariantTensorDerivative D.riemannEvaluation p ![X, v, a, w, b] +
        D.curvatureTensor p (frozenConnectionEndomorphism D p X v) a w b +
        D.curvatureTensor p v (frozenConnectionEndomorphism D p X a) w b +
        D.curvatureTensor p v a (frozenConnectionEndomorphism D p X w) b +
        D.curvatureTensor p v a w (frozenConnectionEndomorphism D p X b) := by
  have h := extensionTensor_derivative D D.riemannEvaluation p X ![v, a, w, b]
  have hzero (z : TangentSpace (𝓡 n) p) :
      Function.update ![v, a, w, b] (0 : Fin 4) z = ![z, a, w, b] := by
    funext i
    fin_cases i <;> simp
  have hone (z : TangentSpace (𝓡 n) p) :
      Function.update ![v, a, w, b] (1 : Fin 4) z = ![v, z, w, b] := by
    funext i
    fin_cases i <;> simp
  have htwo (z : TangentSpace (𝓡 n) p) :
      Function.update ![v, a, w, b] (2 : Fin 4) z = ![v, a, z, b] := by
    funext i
    fin_cases i <;> simp
  have hthree (z : TangentSpace (𝓡 n) p) :
      Function.update ![v, a, w, b] (3 : Fin 4) z = ![v, a, w, z] := by
    funext i
    fin_cases i <;> simp
  simpa [frameCurvatureSlice_apply, Fin.sum_univ_succ, hzero, hone, htwo, hthree,
    LeviCivitaData.riemannEvaluation, add_assoc] using h

end PoincareConjecture.Proofs.M09
