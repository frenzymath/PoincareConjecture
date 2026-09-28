import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CircleAngularGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Atlas










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem saddle_selected_reparametrized_arcs
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (label : Fin 2 ≃ Fin 2) (a v : Fin 2 → ℝ)
    (hv : ∀ i : Fin 2, v i ≠ 0)
    (C1 : Fin 2 → UnitCircle → E2)
    (hC1 : ∀ i : Fin 2, IsPlanarEmbedding (C1 i))
    (hDisjoint : ∀ i k : Fin 2, i ≠ k →
      Disjoint (range (C1 i)) (range (C1 k)))
    (Theta : Fin 2 → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (eta nu : ℝ) :
    let phase : Fin 2 → ℝ → UnitCircle := fun i s =>
      complexUnitCircleHomeomorph (Circle.exp (a i + v i * s))
    let src : Fin 2 → ℝ → UnitTwoSphere := fun i s => q (label i) (phase i s)
    let alpha : Fin 2 → ℝ → E2 := fun i t =>
      C1 (label i) (phase i (Theta i t))
    (∀ i : Fin 2, InjOn (src i) (Icc (-eta) (1 + eta))) →
    (∀ i : Fin 2, MapsTo (Theta i) (Icc (-nu) (1 + nu))
      (Icc (-eta) (1 + eta))) →
    (∀ i : Fin 2, Theta i '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1) →
    (∀ i : Fin 2,
      ContDiff ℝ ∞ (alpha i) ∧
      (∀ t : ℝ, deriv (alpha i) t ≠ 0) ∧
      InjOn (alpha i) (Icc (-nu) (1 + nu))) ∧
    (∀ i k : Fin 2, i ≠ k →
      Disjoint (alpha i '' Icc (-nu) (1 + nu))
        (alpha k '' Icc (-nu) (1 + nu))) ∧
    ∀ i : Fin 2,
      alpha i '' Icc (0 : ℝ) 1 = C1 (label i) '' (phase i '' Icc (0 : ℝ) 1) := by
  dsimp only
  intro hSource hBuffer hInterval
  let phase : Fin 2 → ℝ → UnitCircle := fun i s =>
    complexUnitCircleHomeomorph (Circle.exp (a i + v i * s))
  let alpha : Fin 2 → ℝ → E2 := fun i t =>
    C1 (label i) (phase i (Theta i t))
  have hPhase (i : Fin 2) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (phase i) ∧
      ∀ t : ℝ, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (phase i) t) :=
    circleAffine_smooth_immersion (a i) (v i) (hv i)
  have hInnerSmooth (i : Fin 2) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (phase i ∘ Theta i) :=
    (hPhase i).1.comp (Theta i).contMDiff
  have hInnerImmersion (i : Fin 2) (t : ℝ) :
      Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (phase i ∘ Theta i) t) := by
    rw [mfderiv_comp t ((hPhase i).1.mdifferentiable (by simp) (Theta i t))
      ((Theta i).mdifferentiable (by simp) t)]
    have hTheta := ((Theta i).toOpenPartialHomeomorph_mdifferentiable
      (by simp)).mfderiv_injective (x := t) (mem_univ _)
    exact ((hPhase i).2 (Theta i t)).comp hTheta
  have hSmooth (i : Fin 2) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) ∞ (alpha i) :=
    (hC1 (label i)).1.comp (hInnerSmooth i)
  have hImmersion (i : Fin 2) (t : ℝ) :
      Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) (alpha i) t) := by
    change Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E2)
      (C1 (label i) ∘ (phase i ∘ Theta i)) t)
    rw [mfderiv_comp t ((hC1 (label i)).1.mdifferentiable (by simp)
      (phase i (Theta i t))) ((hInnerSmooth i).mdifferentiable (by simp) t)]
    exact ((hC1 (label i)).2.2 (phase i (Theta i t))).comp (hInnerImmersion i t)
  have hGeometry (i : Fin 2) :
      ContDiff ℝ ∞ (alpha i) ∧
      (∀ t : ℝ, deriv (alpha i) t ≠ 0) ∧
      InjOn (alpha i) (Icc (-nu) (1 + nu)) := by
    refine ⟨(hSmooth i).contDiff, ?_, ?_⟩
    · intro t hz
      have hi : Injective (fderiv ℝ (alpha i) t) := by
        rw [← mfderiv_eq_fderiv]
        exact hImmersion i t
      have hbad : (1 : ℝ) = 0 := hi (by simp [fderiv_eq_smul_deriv, hz])
      exact one_ne_zero hbad
    · intro t ht s hs hts
      have hp := (hC1 (label i)).2.1 hts
      apply (Theta i).injective
      exact hSource i (hBuffer i ht) (hBuffer i hs) (congrArg (q (label i)) hp)
  refine ⟨hGeometry, ?_, ?_⟩
  · intro i k hik
    apply (hDisjoint (label i) (label k) (fun h => hik (label.injective h))).mono
    · rintro x ⟨t, _, rfl⟩
      exact mem_range_self (phase i (Theta i t))
    · rintro x ⟨t, _, rfl⟩
      exact mem_range_self (phase k (Theta k t))
  · intro i
    change (C1 (label i) ∘ (phase i ∘ Theta i)) '' Icc (0 : ℝ) 1 =
      C1 (label i) '' (phase i '' Icc (0 : ℝ) 1)
    rw [image_comp, image_comp, hInterval i]

end PoincareConjecture.M25.Topology3D
