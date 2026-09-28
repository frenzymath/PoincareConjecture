import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityGeometry
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.MetricDuality

set_option autoImplicit false

open scoped InnerProductSpace Manifold ContDiff

namespace PoincareConjecture.M65Interior

variable {S T E : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gramLeftInverse_comp_equiv [FiniteDimensional ℝ S] [FiniteDimensional ℝ T]
    (A : T →L[ℝ] E) (hA : Function.Injective A) (J : S ≃L[ℝ] T) (v : E) :
    gramLeftInverse (A.comp (J : S →L[ℝ] T)) v = J.symm (gramLeftInverse A v) := by
  have hAJ : Function.Injective (A.comp (J : S →L[ℝ] T)) := hA.comp J.injective
  change ((A.comp (J : S →L[ℝ] T)).adjoint.comp
    (A.comp (J : S →L[ℝ] T))).inverse
      ((A.comp (J : S →L[ℝ] T)).adjoint v) = _
  apply (gram_isInvertible _ hAJ).inverse_apply_eq.mpr
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (fun w => (J : S →L[ℝ] T).adjoint w)
    ((gram_isInvertible A hA).self_apply_inverse (A.adjoint v)).symm

noncomputable def coordinateMetric (A : S →L[ℝ] E) (G : S →L[ℝ] S →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp G (gramLeftInverse A) (gramLeftInverse A) +
    (ContinuousLinearMap.bilinearComp (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
      (ContinuousLinearMap.id ℝ E - A.comp (gramLeftInverse A))
      (ContinuousLinearMap.id ℝ E - A.comp (gramLeftInverse A)) : E →L[ℝ] E →L[ℝ] ℝ)

theorem ambientMetric_eq_coordinateMetric [FiniteDimensional ℝ S] [FiniteDimensional ℝ T]
    (A : T →L[ℝ] E) (hA : Function.Injective A) (J : S ≃L[ℝ] T) :
    ambientMetric A = coordinateMetric (A.comp (J : S →L[ℝ] T))
      (ContinuousLinearMap.bilinearComp (innerSL ℝ) (J : S →L[ℝ] T) (J : S →L[ℝ] T)) := by
  have hL (v : E) : J (gramLeftInverse (A.comp (J : S →L[ℝ] T)) v) =
      gramLeftInverse A v := by
    rw [gramLeftInverse_comp_equiv A hA J, J.apply_symm_apply]
  ext v w
  change ⟪gramLeftInverse A v, gramLeftInverse A w⟫_ℝ +
      ⟪v - A (gramLeftInverse A v), w - A (gramLeftInverse A w)⟫_ℝ =
    ⟪J (gramLeftInverse (A.comp (J : S →L[ℝ] T)) v),
      J (gramLeftInverse (A.comp (J : S →L[ℝ] T)) w)⟫_ℝ +
      ⟪v - A (J (gramLeftInverse (A.comp (J : S →L[ℝ] T)) v)),
        w - A (J (gramLeftInverse (A.comp (J : S →L[ℝ] T)) w))⟫_ℝ
  rw [hL, hL]

theorem contDiffAt_gramLeftInverse [FiniteDimensional ℝ S]
    {d : ℕ} {A : EuclideanSpace ℝ (Fin d) → S →L[ℝ] E}
    {x : EuclideanSpace ℝ (Fin d)} (hA : ContDiffAt ℝ ∞ A x)
    (hinj : Function.Injective (A x)) :
    ContDiffAt ℝ ∞ (fun y => gramLeftInverse (A y)) x := by
  have hadj : ContDiffAt ℝ ∞ (fun y => (A y).adjoint) x :=
    (ContinuousLinearMap.adjoint : (S →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] S)).contDiff.contDiffAt.comp x hA
  have hgram := hadj.clm_comp hA
  exact ((gram_isInvertible (A x) hinj).contDiffAt_map_inverse.comp x hgram).clm_comp hadj

theorem contDiffAt_coordinateMetric [FiniteDimensional ℝ S] [FiniteDimensional ℝ E]
    {d : ℕ} {A : EuclideanSpace ℝ (Fin d) → S →L[ℝ] E}
    {G : EuclideanSpace ℝ (Fin d) → S →L[ℝ] S →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin d)} (hA : ContDiffAt ℝ ∞ A x)
    (hG : ContDiffAt ℝ ∞ G x) (hinj : Function.Injective (A x)) :
    ContDiffAt ℝ ∞ (fun y => coordinateMetric (A y) (G y)) x := by
  have hL := contDiffAt_gramLeftInverse hA hinj
  have hLv (v : E) := hL.clm_apply (contDiffAt_const (c := v))
  have hR (v : E) := (contDiffAt_const (c := v)).sub (hA.clm_apply (hLv v))
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffAt_clm_of_apply
  intro v
  apply contMDiffAt_clm_of_apply
  intro w
  exact (((hG.clm_apply (hLv v)).clm_apply (hLv w)).add
    ((hR v).inner ℝ (hR w))).contMDiffAt

end PoincareConjecture.M65Interior
