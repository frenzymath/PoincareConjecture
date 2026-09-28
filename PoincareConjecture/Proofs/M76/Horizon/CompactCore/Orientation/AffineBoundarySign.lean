import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.AffineNormalExtension

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem plLocalSign_affineEquiv (A : E ≃ᴬ[ℝ] E)
    (hA : A.toHomeomorph.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E)
    (x : A.toHomeomorph.toOpenPartialHomeomorph.source) :
    plLocalSign A.toHomeomorph.toOpenPartialHomeomorph hA x =
      SignType.sign (LinearMap.det A.toContinuousAffineMap.toAffineMap.linear) := by
  obtain ⟨B, K, hK, hxK, hKs, hf, t, ht, htc, hxt, _⟩ :=
    exists_plAffineWitness A.toHomeomorph.toOpenPartialHomeomorph hA x.property
  exact plLocalSign_eq_of_witness _ _ _
    ⟨K, hK, hxK, hKs, hf, t, ht, htc, hxt, fun _ _ => rfl⟩

theorem plLocalSign_eq_affineNormalExtension
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    (ell m : E →ᴬ[ℝ] ℝ) (n n' : E) (B : E →ᴬ[ℝ] E)
    (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (hB : ∀ y, ell y = 0 → m (B y) = 0)
    (hi : InjOn B {y | ell y = 0})
    (hside : ∀ y ∈ h.source, 0 ≤ m (h y) ↔ 0 ≤ ell y)
    (hagree : ∀ y ∈ h.source, ell y = 0 → h y = B y)
    (x : h.source) (hx : ell x = 0) :
    plLocalSign h hh x =
      SignType.sign (LinearMap.det (affineNormalExtension ell n n' B).toAffineMap.linear) := by
  obtain ⟨A, hformula, hheight, hplane⟩ :=
    exists_affine_normal_extension ell m n n' B hn hn' hB hi
  have hA : A.toHomeomorph.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E :=
    ⟨locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ⟩
  have heq := plLocalSign_eq_of_halfspace_agreement h
    A.toHomeomorph.toOpenPartialHomeomorph hh hA ell m n hn hside
    (fun y _ => by change 0 ≤ m (A y) ↔ 0 ≤ ell y; rw [hheight])
    (fun y hy he => (hagree y hy.1 he).trans (hplane y he).symm)
    x.property (mem_univ _) hx
  have hmaps : A.toContinuousAffineMap = affineNormalExtension ell n n' B := by
    ext y
    exact hformula y
  exact heq.trans ((plLocalSign_affineEquiv A hA ⟨x, mem_univ _⟩).trans
    (by rw [hmaps]))

end Geometry
