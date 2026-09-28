import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.TangentTestMap
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64ObservedMetric_tangent_diagonal
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hgram : ∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f → ∀ z i j,
      B (f z) (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
          m60AreaGram g f z i j)
    (q : M) (w : TangentSpace (𝓡 n) q) :
    B q (mfderiv (𝓡 n) (𝓡 m) e q w) (mfderiv (𝓡 n) (𝓡 m) e q w) = g.inner q w w := by
  obtain ⟨f, hf, h0, hw⟩ := m64_exists_smooth_tangent_test q w
  have hobs : fderiv ℝ (e ∘ f) 0 (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      mfderiv (𝓡 n) (𝓡 m) e q w := by
    have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 n) (I'' := 𝓡 m)
      (f := f) (g := e) (0 : LoopPlane)
      (he.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _)
    have h := congrArg (fun L => L (EuclideanSpace.basisFun (Fin 2) ℝ 0)) hcomp
    rw [mfderiv_eq_fderiv] at h
    change fderiv ℝ (e ∘ f) 0 (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      mfderiv (𝓡 n) (𝓡 m) e (f 0)
        (mfderiv (𝓡 2) (𝓡 n) f 0 (EuclideanSpace.basisFun (Fin 2) ℝ 0)) at h
    erw [hw, h0] at h
    exact h
  have h := hgram f hf 0 0 0
  erw [hobs, h0] at h
  change B q _ _ = g.inner (f 0)
    (mfderiv (𝓡 2) (𝓡 n) f 0 (EuclideanSpace.basisFun (Fin 2) ℝ 0))
    (mfderiv (𝓡 2) (𝓡 n) f 0 (EuclideanSpace.basisFun (Fin 2) ℝ 0)) at h
  erw [hw, h0] at h
  exact h

theorem m64ObservedMetric_tangent_coercivity [CompactSpace M]
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hgram : ∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f → ∀ z i j,
      B (f z) (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ (e ∘ f) z (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
          m60AreaGram g f z i j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨D, hD, hbound⟩ := M60.exists_uniform_mfderiv_bound g e he
  refine ⟨D ^ 2, sq_nonneg D, ?_⟩
  rintro q v ⟨w, rfl⟩
  have hnorm : ‖(show E from mfderiv (𝓡 n) (𝓡 m) e q w)‖ ≤ D * ‖w‖ := by
    rw [← norm_tangentSpace_vectorSpace (x := e q)]
    exact ((mfderiv (𝓡 n) (𝓡 m) e q).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg w))
  have hnormsq : ‖w‖ ^ 2 = g.inner q w w := (real_inner_self_eq_norm_sq w).symm
  have hdiag := m64ObservedMetric_tangent_diagonal g e he B hgram q w
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg w))).mpr hnorm
  simpa only [mul_pow, hnormsq, hdiag] using hs

end PoincareConjecture
