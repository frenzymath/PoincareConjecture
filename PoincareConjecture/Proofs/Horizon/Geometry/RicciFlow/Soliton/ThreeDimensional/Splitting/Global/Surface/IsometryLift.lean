import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.DeckAction
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Matrix Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RicciFlow.Splitting

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem exists_orthogonal_surface_isometry_lift
    (g : RiemannianMetric 2 M) (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) (hsurj : Function.Surjective q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 2) (𝓡 2) q x u) (mfderiv (𝓡 2) (𝓡 2) q x v) =
        (roundSphereMetric 2).inner x u v)
    (σ : M ≃ₘ⟮𝓡 2, 𝓡 2⟯ M)
    (hσ : ∀ x u v, g.inner (σ x)
      (mfderiv (𝓡 2) (𝓡 2) σ x u) (mfderiv (𝓡 2) (𝓡 2) σ x v) =
        g.inner x u v) :
    ∃ L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∀ x, q (sphereMotion L x) = σ (q x) := by
  let x : UnitSphere 2 := ⟨EuclideanSpace.single 0 1, by simp [UnitSphere]⟩
  obtain ⟨y, hy⟩ := hsurj (σ (q x))
  let Lx := hq.mfderivToContinuousLinearEquiv (by simp) x
  let Ly := hq.mfderivToContinuousLinearEquiv (by simp) y
  let Lσ := σ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) (q x)
  let A : TangentSpace (𝓡 2) x ≃L[ℝ] TangentSpace (𝓡 2) y :=
    (Lx.trans Lσ).trans Ly.symm
  have hA (u v : TangentSpace (𝓡 2) x) :
      (roundSphereMetric 2).inner y (A u) (A v) =
        (roundSphereMetric 2).inner x u v := by
    rw [← hmetric y (A u) (A v)]
    change g.inner (q y) (Ly (Ly.symm (Lσ (Lx u))))
      (Ly (Ly.symm (Lσ (Lx v)))) = _
    rw [Ly.apply_symm_apply, Ly.apply_symm_apply, hy]
    exact (hσ (q x) (Lx u) (Lx v)).trans (hmetric x u v)
  obtain ⟨L, hpos, hder⟩ := exists_ambient_sphere_motion_firstOrder x y A hA
  refine ⟨L, ?_⟩
  have hleft : ContMDiff (𝓡 2) (𝓡 2) ∞ (q ∘ sphereMotion L) :=
    hq.contMDiff.comp (sphereMotion L).contMDiff
  have hright : ContMDiff (𝓡 2) (𝓡 2) ∞ (σ ∘ q) :=
    σ.contMDiff.comp hq.contMDiff
  have hleftmetric (z : UnitSphere 2) (u v : TangentSpace (𝓡 2) z) :
      (roundSphereMetric 2).inner z u v = g.inner ((q ∘ sphereMotion L) z)
        (mfderiv (𝓡 2) (𝓡 2) (q ∘ sphereMotion L) z u)
        (mfderiv (𝓡 2) (𝓡 2) (q ∘ sphereMotion L) z v) := by
    rw [mfderiv_comp z (hq.mdifferentiable (by simp) _)
      ((sphereMotion L).contMDiffAt.mdifferentiableAt (by simp))]
    exact (sphereMotion_inner L z u v).symm.trans (hmetric _ _ _).symm
  have hrightmetric (z : UnitSphere 2) (u v : TangentSpace (𝓡 2) z) :
      (roundSphereMetric 2).inner z u v = g.inner ((σ ∘ q) z)
        (mfderiv (𝓡 2) (𝓡 2) (σ ∘ q) z u)
        (mfderiv (𝓡 2) (𝓡 2) (σ ∘ q) z v) := by
    rw [mfderiv_comp z (σ.contMDiffAt.mdifferentiableAt (by simp))
      (hq.mdifferentiable (by simp) _)]
    exact (hmetric z u v).symm.trans (hσ _ _ _).symm
  have hderiv : mfderiv (𝓡 2) (𝓡 2) (q ∘ sphereMotion L) x =
      mfderiv (𝓡 2) (𝓡 2) (σ ∘ q) x := by
    rw [mfderiv_comp x (hq.mdifferentiable (by simp) _)
      ((sphereMotion L).contMDiffAt.mdifferentiableAt (by simp)),
      mfderiv_comp x (σ.contMDiffAt.mdifferentiableAt (by simp))
        (hq.mdifferentiable (by simp) _)]
    ext v
    change mfderiv (𝓡 2) (𝓡 2) q (sphereMotion L x)
      (mfderiv (𝓡 2) (𝓡 2) (sphereMotion L) x v) = _
    rw [hder]
    erw [hpos]
    change Ly (Ly.symm (Lσ (Lx v))) = Lσ (Lx v)
    exact Ly.apply_symm_apply _
  have heq := PoincareConjecture.SpaceForm.local_isometry_eqOn_of_firstOrder
    (roundSphereMetric 2) g isOpen_univ isPreconnected_univ
    hleft.contMDiffOn hright.contMDiffOn
    (fun z _ u v => hleftmetric z u v)
    (fun z _ u v => hrightmetric z u v) (mem_univ x)
    (by simpa only [Function.comp_apply, hpos] using hy) hderiv
  exact fun z => heq (mem_univ z)

theorem orthogonalThree_exists_fixed_or_negated_unit_vector
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    ∃ v : EuclideanSpace ℝ (Fin 3), ‖v‖ = 1 ∧ (L v = v ∨ L v = -v) := by
  let A := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearEquiv.toLinearMap
  have hA : A * A.transpose = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff _ _).mp
      (L.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin 3) ℝ)
        (EuclideanSpace.basisFun (Fin 3) ℝ))
  have happly (v : EuclideanSpace ℝ (Fin 3)) :
      A *ᵥ WithLp.ofLp v = WithLp.ofLp (L v) := by
    have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearEquiv.toLinearMap v
    have hrepr (w : EuclideanSpace ℝ (Fin 3)) :
        ⇑((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr w) = WithLp.ofLp w := by
      funext i
      rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    rw [hrepr v, hrepr (L.toLinearEquiv.toLinearMap v)] at h
    exact h
  have hdet : (A - A.transpose).det = 0 := by
    have hneg : (A - A.transpose).det = -(A - A.transpose).det := by
      calc
        _ = (A - A.transpose).transpose.det := (Matrix.det_transpose _).symm
        _ = -(A - A.transpose).det := by
          simp only [Matrix.transpose_sub, Matrix.transpose_transpose]
          rw [show A.transpose - A = -(A - A.transpose) by abel, Matrix.det_neg]
          norm_num
    linarith
  obtain ⟨w, hw, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have heq : A *ᵥ w = A.transpose *ᵥ w := by
    simpa only [Matrix.sub_mulVec, sub_eq_zero] using hzero
  let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 w
  have hv : v ≠ 0 := by
    intro hz
    exact hw (congrArg WithLp.ofLp hz)
  have hsq : L (L v) = v := by
    apply WithLp.ofLp_injective
    rw [← happly, ← happly]
    change A *ᵥ (A *ᵥ w) = w
    rw [heq, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  have hex : ∃ u : EuclideanSpace ℝ (Fin 3), u ≠ 0 ∧ (L u = u ∨ L u = -u) := by
    by_cases hplus : L v + v = 0
    · exact ⟨v, hv, Or.inr (eq_neg_of_add_eq_zero_left hplus)⟩
    · refine ⟨L v + v, hplus, Or.inl ?_⟩
      rw [L.map_add, hsq, add_comm]
  obtain ⟨u, hu, hLu⟩ := hex
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
      inv_mul_cancel₀ hn]
  · rcases hLu with hfix | hneg
    · exact Or.inl (by rw [L.map_smul, hfix])
    · exact Or.inr (by rw [L.map_smul, hneg, smul_neg])

theorem surface_isometry_has_fixed_point_of_antipodal_cover
    (g : RiemannianMetric 2 M) (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) (hsurj : Function.Surjective q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 2) (𝓡 2) q x u) (mfderiv (𝓡 2) (𝓡 2) q x v) =
        (roundSphereMetric 2).inner x u v)
    (hanti : ∀ x, q (-x) = q x)
    (σ : M ≃ₘ⟮𝓡 2, 𝓡 2⟯ M)
    (hσ : ∀ x u v, g.inner (σ x)
      (mfderiv (𝓡 2) (𝓡 2) σ x u) (mfderiv (𝓡 2) (𝓡 2) σ x v) =
        g.inner x u v) :
    ∃ x, σ x = x := by
  obtain ⟨L, hL⟩ := exists_orthogonal_surface_isometry_lift g q hq hsurj hmetric σ hσ
  obtain ⟨v, hn, hfix | hneg⟩ := orthogonalThree_exists_fixed_or_negated_unit_vector L
  · let x : UnitSphere 2 := ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩
    refine ⟨q x, ?_⟩
    rw [← hL x]
    exact congrArg q (Subtype.ext hfix)
  · let x : UnitSphere 2 := ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩
    refine ⟨q x, ?_⟩
    rw [← hL x]
    exact (congrArg q (show sphereMotion L x = -x from Subtype.ext hneg)).trans (hanti x)

theorem surface_cover_injective_of_free_isometry
    (g : RiemannianMetric 2 M) (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) (hsurj : Function.Surjective q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 2) (𝓡 2) q x u) (mfderiv (𝓡 2) (𝓡 2) q x v) =
        (roundSphereMetric 2).inner x u v)
    (σ : M ≃ₘ⟮𝓡 2, 𝓡 2⟯ M)
    (hσ : ∀ x u v, g.inner (σ x)
      (mfderiv (𝓡 2) (𝓡 2) σ x u) (mfderiv (𝓡 2) (𝓡 2) σ x v) =
        g.inner x u v)
    (hfree : ∀ x, σ x ≠ x) : Function.Injective q := by
  rcases orthogonalSurfaceDeckGroup_fiber_dichotomy g q hq hmetric with hinj | hpair
  · exact hinj
  · have hanti (x : UnitSphere 2) : q (-x) = q x :=
      ((hpair x (-x)).mpr (Or.inr rfl)).symm
    obtain ⟨x, hx⟩ := surface_isometry_has_fixed_point_of_antipodal_cover
      g q hq hsurj hmetric hanti σ hσ
    exact (hfree x hx).elim

end PoincareConjecture.RicciFlow.Splitting
