import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.FrameChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

theorem connection_eq_of_eventuallyEq_along_curve
    (D : LeviCivitaData g) {γ : ℝ → S} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ t)
    {T W : (x : S) → TangentSpace (𝓡 2) x}
    (hT : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% T) (γ t))
    (hW : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% W) (γ t))
    (heq : ∀ᶠ s in 𝓝 t, T (γ s) = W (γ s)) :
    D.connection T (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) =
      D.connection W (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) := by
  obtain ⟨U, e₁, e₂, hU, ht, he₁, he₂, hu₁, hu₂, ho⟩ :=
    g.exists_local_orthonormal_frame (γ t)
  let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1
  have hchain (f : S → ℝ) (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (γ t)) :
      mvfderiv (𝓡 2) f (γ t) v = deriv (f ∘ γ) t := by
    have h := congrArg (fun L => L 1) (mvfderiv_comp t hf hγ)
    simp only [ContinuousLinearMap.comp_apply] at h
    have hd : mvfderiv 𝓘(ℝ, ℝ) (f ∘ γ) t 1 = deriv (f ∘ γ) t := by
      simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
      rfl
    rw [hd] at h
    exact h.symm
  have hcoord (e : (x : S) → TangentSpace (𝓡 2) x)
      (he : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% e) (γ t)) :
      g.inner (γ t) (D.connection T (γ t) v) (e (γ t)) =
        g.inner (γ t) (D.connection W (γ t) v) (e (γ t)) := by
    have hTe := D.horizon_mvfderiv_inner (FiberBundle.extend (EuclideanSpace ℝ (Fin 2)) v) hT he
    have hWe := D.horizon_mvfderiv_inner (FiberBundle.extend (EuclideanSpace ℝ (Fin 2)) v) hW he
    simp only [covariantDerivativeOnFields, FiberBundle.extend_apply_self] at hTe hWe
    have hinner (A : (x : S) → TangentSpace (𝓡 2) x)
        (hA : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% A) (γ t)) :
        MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (fun y => g.inner y (A y) (e y)) (γ t) := by
      have hA' := ((g.contMDiff (γ t)).mdifferentiableAt (by simp)).clm_bundle_apply hA
      simpa using (mdifferentiableAt_totalSpace (𝓡 2) _).mp
        (hA'.clm_bundle_apply he) |>.2
    rw [hchain _ (hinner T hT)] at hTe
    rw [hchain _ (hinner W hW)] at hWe
    have hcoeff : (fun s => g.inner (γ s) (T (γ s)) (e (γ s))) =ᶠ[𝓝 t]
        (fun s => g.inner (γ s) (W (γ s)) (e (γ s))) :=
      heq.mono fun s hs => by dsimp only; rw [hs]
    have hd := hcoeff.deriv_eq
    dsimp only [Function.comp_def] at hTe hWe
    rw [heq.self_of_nhds] at hTe
    linarith
  rw [g.eq_frameCoordinates_smul (γ t) (hu₁ _ ht) (hu₂ _ ht) (ho _ ht)
    (D.connection T (γ t) v),
    g.eq_frameCoordinates_smul (γ t) (hu₁ _ ht) (hu₂ _ ht) (ho _ ht)
    (D.connection W (γ t) v)]
  rw [hcoord e₁ ((he₁.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp)),
    hcoord e₂ ((he₂.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp))]

theorem surfaceTurningForm_eq_of_eventuallyEq_along_curve
    (D : LeviCivitaData g) {γ : ℝ → S} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ t)
    (e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x)
    {T W V Z : (x : S) → TangentSpace (𝓡 2) x}
    (hT : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% T) (γ t))
    (hW : MDifferentiableAt (𝓡 2) ((𝓡 2).prod (𝓡 2)) (T% W) (γ t))
    (heq : ∀ᶠ s in 𝓝 t, T (γ s) = W (γ s))
    (hV : V (γ t) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1)
    (hZ : Z (γ t) = mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1) :
    D.surfaceTurningForm e₁ e₂ T V (γ t) =
      D.surfaceTurningForm e₁ e₂ W Z (γ t) := by
  simp only [surfaceTurningForm, hV, hZ,
    D.connection_eq_of_eventuallyEq_along_curve hγ hT hW heq, heq.self_of_nhds]

end PoincareConjecture.LeviCivitaData
