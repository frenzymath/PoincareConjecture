import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

open scoped InnerProductSpace Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M65Interior

variable {T E : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [CompleteSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def gramLeftInverse (A : T →L[ℝ] E) : E →L[ℝ] T :=
  (A.adjoint.comp A).inverse.comp A.adjoint

theorem gram_isInvertible [FiniteDimensional ℝ T] (A : T →L[ℝ] E)
    (hA : Function.Injective A) : (A.adjoint.comp A).IsInvertible := by
  have hi : Function.Injective (A.adjoint.comp A) :=
    A.adjoint_comp_self_injective_iff.mpr hA
  have hs : Function.Surjective (A.adjoint.comp A) :=
    LinearMap.injective_iff_surjective.mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (A.adjoint.comp A)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem gramLeftInverse_apply_image [FiniteDimensional ℝ T] (A : T →L[ℝ] E)
    (hA : Function.Injective A) (v : T) : gramLeftInverse A (A v) = v := by
  exact (gram_isInvertible A hA).inverse_apply_self v

noncomputable def ambientMetric (A : T →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (innerSL ℝ) (gramLeftInverse A) (gramLeftInverse A) +
    ContinuousLinearMap.bilinearComp (innerSL ℝ)
      (ContinuousLinearMap.id ℝ E - A.comp (gramLeftInverse A))
      (ContinuousLinearMap.id ℝ E - A.comp (gramLeftInverse A))

theorem ambientMetric_apply (A : T →L[ℝ] E) (v w : E) :
    ambientMetric A v w =
      ⟪gramLeftInverse A v, gramLeftInverse A w⟫_ℝ +
        ⟪v - A (gramLeftInverse A v), w - A (gramLeftInverse A w)⟫_ℝ := by
  rfl

theorem ambientMetric_symmetric (A : T →L[ℝ] E) (v w : E) :
    ambientMetric A v w = ambientMetric A w v := by
  simp only [ambientMetric_apply, real_inner_comm]

theorem ambientMetric_self (A : T →L[ℝ] E) (v : E) :
    ambientMetric A v v = ‖gramLeftInverse A v‖ ^ 2 +
      ‖v - A (gramLeftInverse A v)‖ ^ 2 := by
  simp only [ambientMetric_apply, real_inner_self_eq_norm_sq]

theorem ambientMetric_pos (A : T →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ambientMetric A v v := by
  rw [ambientMetric_self]
  by_cases hL : gramLeftInverse A v = 0
  · simpa only [hL, norm_zero, zero_pow (by decide : 2 ≠ 0), map_zero, sub_zero,
      zero_add] using sq_pos_of_pos (norm_pos_iff.mpr hv)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hL)) (sq_nonneg _)

theorem ambientMetric_image [FiniteDimensional ℝ T] (A : T →L[ℝ] E)
    (hA : Function.Injective A) (v w : T) : ambientMetric A (A v) (A w) = ⟪v,w⟫_ℝ := by
  simp only [ambientMetric_apply, gramLeftInverse_apply_image A hA,
    sub_self, inner_zero_left, add_zero]

end PoincareConjecture.M65Interior

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}

noncomputable def m65EmbeddingTangentLeftInverse (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] TangentSpace (𝓡 3) p := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) p
  have : CompleteSpace (TangentSpace (𝓡 3) p) := FiniteDimensional.complete ℝ _
  exact M65Interior.gramLeftInverse (mfderiv (𝓡 3) (𝓡 N) e p)

noncomputable def m65EmbeddingMetric (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) p
  have : CompleteSpace (TangentSpace (𝓡 3) p) := FiniteDimensional.complete ℝ _
  exact M65Interior.ambientMetric (mfderiv (𝓡 3) (𝓡 N) e p)

theorem m65EmbeddingTangentLeftInverse_apply (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M)
    (he : Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (v : TangentSpace (𝓡 3) p) :
    m65EmbeddingTangentLeftInverse g e p (mfderiv (𝓡 3) (𝓡 N) e p v) = v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) p
  have : CompleteSpace (TangentSpace (𝓡 3) p) := FiniteDimensional.complete ℝ _
  exact M65Interior.gramLeftInverse_apply_image (E := EuclideanSpace ℝ (Fin N))
    (mfderiv (𝓡 3) (𝓡 N) e p) he v

theorem m65EmbeddingMetric_pos (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M) {v : EuclideanSpace ℝ (Fin N)}
    (hv : v ≠ 0) : 0 < m65EmbeddingMetric g e p v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) p
  have : CompleteSpace (TangentSpace (𝓡 3) p) := FiniteDimensional.complete ℝ _
  exact M65Interior.ambientMetric_pos (E := EuclideanSpace ℝ (Fin N))
    (mfderiv (𝓡 3) (𝓡 N) e p) hv

theorem m65EmbeddingMetric_image (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M)
    (he : Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (v w : TangentSpace (𝓡 3) p) :
    m65EmbeddingMetric g e p (mfderiv (𝓡 3) (𝓡 N) e p v)
      (mfderiv (𝓡 3) (𝓡 N) e p w) = g.inner p v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) p
  have : CompleteSpace (TangentSpace (𝓡 3) p) := FiniteDimensional.complete ℝ _
  exact M65Interior.ambientMetric_image (E := EuclideanSpace ℝ (Fin N))
    (mfderiv (𝓡 3) (𝓡 N) e p) he v w

end PoincareConjecture
