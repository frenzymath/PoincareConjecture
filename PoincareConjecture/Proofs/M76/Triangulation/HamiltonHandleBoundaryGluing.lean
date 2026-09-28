import PoincareConjecture.Proofs.M76.Mathlib.LocalPLHalfspaceGluing
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinder









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76



def handleTransverseStrip (J : Finset (Fin 3)) : Set (Fin 3 → ℝ) :=
  {x | ∀ i, i ∉ J → |x i| < 1}



theorem isOpen_handleTransverseStrip (J : Finset (Fin 3)) :
    IsOpen (handleTransverseStrip J) := by
  have hrep : handleTransverseStrip J =
      ⋂ i : Fin 3, ⋂ (_ : i ∉ J), {x : Fin 3 → ℝ | |x i| < 1} := by
    ext x
    simp [handleTransverseStrip]
  rw [hrep]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i).abs continuous_const





theorem locallyPiecewiseAffineOn_handle_attaching_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset (Fin 3)) {f g : (Fin 3 → ℝ) → E} {N : Set (Fin 3 → ℝ)}
    (hf : LocallyPiecewiseAffineOn f N)
    (hg : FinitePiecewiseAffineOn g (closedBall (0 : Fin 3 → ℝ) 1))
    (hfixed : EqOn g f ((coordinateCylinder J)ᶜ ∪ frontier (coordinateCylinder J))) :
    LocallyPiecewiseAffineOn g (N ∩ handleTransverseStrip J) := by
  classical
  let L : J × Bool → (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
    fun j => if j.2 then LinearMap.proj j.1.val else -(LinearMap.proj j.1.val)
  have hL (j : J × Bool) : L j ≠ 0 := by
    intro h
    have hv := congrArg (fun l : (Fin 3 → ℝ) →ₗ[ℝ] ℝ =>
      l (Function.update (0 : Fin 3 → ℝ) j.1 1)) h
    rcases j with ⟨i, b⟩
    cases b <;> simp [L] at hv
  have hrep : coordinateCylinder J = {x | ∀ j : J × Bool, L j x ≤ 1} := by
    ext x
    constructor
    · intro hx j
      rcases j with ⟨i, b⟩
      have hi := abs_le.mp (hx i i.property)
      cases b
      · change -(x i) ≤ 1
        linarith [hi.1]
      · exact hi.2
    · intro hx i hi
      have hp := hx (⟨i, hi⟩, true)
      have hn := hx (⟨i, hi⟩, false)
      change x i ≤ 1 at hp
      change -(x i) ≤ 1 at hn
      exact abs_le.mpr ⟨by linarith, hp⟩
  apply locallyPiecewiseAffineOn_of_halfspace_replacement
    (hf.mono (hf.isOpen.inter (isOpen_handleTransverseStrip J)) inter_subset_left)
    hg L hL hrep
  · rintro x ⟨⟨_, hxstrip⟩, hxcyl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    by_cases hi : i ∈ J
    · exact hxcyl i hi
    · exact (hxstrip i hi).le
  · intro x hx
    apply hfixed
    by_cases hxcyl : x ∈ coordinateCylinder J
    · exact Or.inr ⟨subset_closure hxcyl, hx.2⟩
    · exact Or.inl hxcyl

end PoincareConjecture.M76
