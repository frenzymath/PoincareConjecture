import PoincareConjecture.Proofs.M10.CurveCalculus
import PoincareConjecture.Proofs.M10.MinimizingLifts
import Mathlib.Analysis.Calculus.Deriv.Pow









set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem curve_energy_continuousOn (g : RiemannianMetric n M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ U) :
    ContinuousOn (fun s ↦ g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  have hsection : Continuous
      (fun t : ℝ ↦ (⟨t, (1 : ℝ)⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph (𝓘(ℝ, ℝ))).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hD := hγ.continuousOn_tangentMapWithin le_rfl hU.uniqueMDiffOn
  have hv : ContinuousOn (fun t : ℝ ↦ (⟨γ t,
      mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) γ U t 1⟩ : TangentBundle (𝓡 n) M)) U :=
    hD.comp hsection.continuousOn (fun _ ht ↦ ht)
  apply (hv.inner_bundle hv).congr
  intro s hs
  change g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s) = _
  simp only [curveVelocity, mfderivWithin_of_mem_nhds (hU.mem_nhds hs)]
  rfl


theorem curve_energy_eq_of_eventuallyEq (g : RiemannianMetric n M)
    {γ η : ℝ → M} {s : ℝ} (h : γ =ᶠ[𝓝 s] η) :
    g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s) =
      g.inner (η s) (curveVelocity η s) (curveVelocity η s) := by
  unfold curveVelocity
  rw [h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n), h.eq_of_nhds]

set_option backward.isDefEq.respectTransparency false in

theorem curve_energy_comp_square (g : RiemannianMetric n M) {γ : ℝ → M} {s : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2)) :
    g.inner (γ (s ^ 2)) (curveVelocity (fun r : ℝ ↦ γ (r ^ 2)) s)
        (curveVelocity (fun r : ℝ ↦ γ (r ^ 2)) s) =
      (2 * s) ^ 2 * g.inner (γ (s ^ 2))
        (curveVelocity γ (s ^ 2)) (curveVelocity γ (s ^ 2)) := by
  have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hc := mfderiv_comp (f := fun r : ℝ ↦ r ^ 2) s hγ
    hsq.differentiableAt.mdifferentiableAt
  simp only [Function.comp_def] at hc
  unfold curveVelocity
  rw [hc, mfderiv_eq_fderiv, hsq.hasFDerivAt.fderiv]
  have hv : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2) (2 * s) =
      (2 * s) • mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2) 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2)).map_smul (2 * s) (1 : ℝ)
  simp only [ContinuousLinearMap.comp_apply]
  change g.inner (γ (s ^ 2))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2) (1 * (2 * s)))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2) (1 * (2 * s))) = _
  rw [one_mul, hv]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end PoincareConjecture.M10
