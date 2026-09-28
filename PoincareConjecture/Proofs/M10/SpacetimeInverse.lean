import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set
open scoped Topology ContDiff

namespace PoincareConjecture.M10

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem endpoint_time_linear_bijective (D : (X × ℝ) →L[ℝ] Y)
    (hD : Function.Bijective (fun h : X ↦ D (h, 0))) :
    Function.Bijective (D.prod (ContinuousLinearMap.snd ℝ X ℝ)) := by
  constructor
  · intro a b hab
    change (D a, a.2) = (D b, b.2) at hab
    have ht : a.2 = b.2 := congrArg (fun z : Y × ℝ ↦ z.2) hab
    have hx : D a = D b := congrArg (fun z : Y × ℝ ↦ z.1) hab
    apply Prod.ext _ ht
    apply hD.1
    have hsplit (z : X × ℝ) : D z = D (z.1, 0) + D (0, z.2) := by
      rw [← map_add]
      congr 1
      simp
    rw [hsplit a, hsplit b, ht] at hx
    exact add_right_cancel hx
  · rintro ⟨y, t⟩
    obtain ⟨x, hx⟩ := hD.2 (y - D (0, t))
    change D (x, 0) = y - D (0, t) at hx
    refine ⟨(x, t), Prod.ext ?_ rfl⟩
    change D (x, t) = y
    have hsplit : (x, t) = (x, 0) + (0, t) := by simp
    rw [hsplit, map_add, hx, sub_add_cancel]

variable [FiniteDimensional ℝ X]

theorem exists_smooth_endpoint_time_inverse {E : X × ℝ → Y} {z₀ : X × ℝ}
    {k : ℕ∞ω} (hE : ContDiffAt ℝ k E z₀) (hk : k ≠ 0)
    (hcrit : Function.Bijective (fun h : X ↦ fderiv ℝ E z₀ (h, 0))) :
    ∃ φ : OpenPartialHomeomorph (X × ℝ) (Y × ℝ),
      (∀ z, φ z = (E z, z.2)) ∧ z₀ ∈ φ.source ∧
      ContDiffAt ℝ k φ.symm (E z₀, z₀.2) ∧
      ∀ w ∈ φ.target, (φ.symm w).2 = w.2 := by
  let H : X × ℝ → Y × ℝ := fun z ↦ (E z, z.2)
  let D : (X × ℝ) →L[ℝ] Y × ℝ :=
    (fderiv ℝ E z₀).prod (ContinuousLinearMap.snd ℝ X ℝ)
  have hD : Function.Bijective D := endpoint_time_linear_bijective _ hcrit
  let e : (X × ℝ) ≃L[ℝ] Y × ℝ :=
    (LinearEquiv.ofBijective D.toLinearMap hD).toContinuousLinearEquiv
  have hH : ContDiffAt ℝ k H z₀ := hE.prodMk contDiffAt_snd
  have hdH : HasFDerivAt H (e : (X × ℝ) →L[ℝ] Y × ℝ) z₀ := by
    exact (hE.differentiableAt hk).hasFDerivAt.prodMk hasFDerivAt_snd
  let φ := hH.toOpenPartialHomeomorph H hdH hk
  refine ⟨φ, fun _ ↦ rfl, hH.mem_toOpenPartialHomeomorph_source hdH hk,
    hH.to_localInverse hdH hk, ?_⟩
  intro w hw
  exact congrArg Prod.snd (φ.right_inv hw)

end PoincareConjecture.M10
