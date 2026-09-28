import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerHandleCorrection
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

noncomputable def hamiltonHandleSplit (J : Finset (Fin 3)) :
    ((J ⊕ {i : Fin 3 // i ∉ J}) → ℝ) ≃ᴬ[ℝ] (Fin 3 → ℝ) := by
  classical
  exact (LinearEquiv.piCongrLeft' ℝ (fun _ : J ⊕ {i : Fin 3 // i ∉ J} => ℝ)
    (Equiv.sumCompl (fun i : Fin 3 => i ∈ J))).toAffineEquiv.toContinuousAffineEquiv

theorem hamiltonHandleSplit_norm (J : Finset (Fin 3))
    (x : (J ⊕ {i : Fin 3 // i ∉ J}) → ℝ) : ‖hamiltonHandleSplit J x‖ = ‖x‖ := by
  classical
  let a := hamiltonHandleSplit J
  let b := Equiv.sumCompl (fun i : Fin 3 => i ∈ J)
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    change ‖x (b.symm i)‖ ≤ ‖x‖
    exact norm_le_pi_norm x _
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (a x))).mpr
    intro i
    have hi := norm_le_pi_norm (a x) (b i)
    change ‖x (b.symm (b i))‖ ≤ ‖a x‖ at hi
    simpa only [b.symm_apply_apply] using hi

theorem hamiltonHandleSplit_mem_cylinder (J : Finset (Fin 3))
    (x : (J ⊕ {i : Fin 3 // i ∉ J}) → ℝ) :
    x ∈ coordinateCylinder (Finset.univ.map
      (Function.Embedding.inl : J ↪ J ⊕ {i : Fin 3 // i ∉ J})) ↔
      hamiltonHandleSplit J x ∈ coordinateCylinder J := by
  classical
  constructor
  · intro hx i hi
    have h := hx (Sum.inl ⟨i, hi⟩)
      (Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩)
    change |x ((Equiv.sumCompl (fun i : Fin 3 => i ∈ J)).symm i)| ≤ 1
    rw [Equiv.sumCompl_symm_apply_of_pos hi]
    exact h
  · intro hx i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    have h := hx j j.property
    change |x ((Equiv.sumCompl (fun i : Fin 3 => i ∈ J)).symm j)| ≤ 1 at h
    rw [Equiv.sumCompl_symm_apply_of_pos j.property] at h
    exact h

theorem exists_hamilton_correction_in_original_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : Finset (Fin 3)) (h : (Fin 3 → ℝ) → E)
    (B : ((J ⊕ {i : Fin 3 // i ∉ J}) → ℝ) ≃ₜ ((J ⊕ {i : Fin 3 // i ∉ J}) → ℝ))
    (hBPL : FinitePiecewiseAffineOn ((h ∘ hamiltonHandleSplit J) ∘ B)
      (closedBall 0 1))
    (hBH : Nonempty (ContinuousMap.HomotopyWith
      (ContinuousMap.id ((J ⊕ {i : Fin 3 // i ∉ J}) → ℝ)) ⟨B, B.continuous⟩
      (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
        ∀ x ∈ (coordinateCylinder (Finset.univ.map
          (Function.Embedding.inl : J ↪ J ⊕ {i : Fin 3 // i ∉ J})))ᶜ ∪
          frontier (coordinateCylinder (Finset.univ.map
            (Function.Embedding.inl : J ↪ J ⊕ {i : Fin 3 // i ∉ J}))), f x = x))) :
    ∃ C : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ),
      (∀ x, C x = hamiltonHandleSplit J (B ((hamiltonHandleSplit J).symm x))) ∧
      FinitePiecewiseAffineOn (h ∘ C) (closedBall 0 1) ∧
      Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id (Fin 3 → ℝ)) ⟨C, C.continuous⟩
        (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
          ∀ x ∈ (coordinateCylinder J)ᶜ ∪ frontier (coordinateCylinder J), f x = x)) := by
  let a := hamiltonHandleSplit J
  let C := a.symm.toHomeomorph.trans (B.trans a.toHomeomorph)
  obtain ⟨H⟩ := hBH
  have hnorminv (x : Fin 3 → ℝ) : ‖a.symm x‖ = ‖x‖ := by
    have hh : ‖a (a.symm x)‖ = ‖a.symm x‖ := hamiltonHandleSplit_norm J (a.symm x)
    rw [a.apply_symm_apply] at hh
    exact hh.symm
  have hball : a '' closedBall (0 : (J ⊕ {i : Fin 3 // i ∉ J}) → ℝ) 1 =
      closedBall (0 : Fin 3 → ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply mem_closedBall_zero_iff.mpr
      rw [show ‖a y‖ = ‖y‖ from hamiltonHandleSplit_norm J y]
      exact mem_closedBall_zero_iff.mp hy
    · intro hx
      exact ⟨a.symm x, by simpa only [mem_closedBall_zero_iff, hnorminv] using hx,
        a.apply_symm_apply x⟩
  have hCPL : FinitePiecewiseAffineOn (h ∘ C) (closedBall (0 : Fin 3 → ℝ) 1) := by
    have hh := hBPL.precomp_affineEquiv a.symm
    change FinitePiecewiseAffineOn (fun x => h (a (B (a.symm x))))
      (a '' closedBall (0 : (J ⊕ {i : Fin 3 // i ∉ J}) → ℝ) 1) at hh
    rw [hball] at hh
    exact hh
  have hCout (x : Fin 3 → ℝ) (hx : 2 ≤ ‖x‖) : C x = x := by
    have hfix := (H.prop 1).2.1 (a.symm x) (by rwa [hnorminv])
    change H (1, a.symm x) = a.symm x at hfix
    rw [H.apply_one] at hfix
    change B (a.symm x) = a.symm x at hfix
    change a (B (a.symm x)) = x
    rw [hfix, a.apply_symm_apply]
  have hCrel (x : Fin 3 → ℝ) (hx : x ∉ coordinateCylinder J) : C x = x := by
    have hmem : a.symm x ∉ coordinateCylinder (Finset.univ.map
        (Function.Embedding.inl : J ↪ J ⊕ {i : Fin 3 // i ∉ J})) := by
      intro hy
      have hm : a (a.symm x) ∈ coordinateCylinder J :=
        (hamiltonHandleSplit_mem_cylinder J (a.symm x)).mp hy
      rw [a.apply_symm_apply] at hm
      exact hx hm
    have hfix := (H.prop 1).2.2 (a.symm x) (Or.inl hmem)
    change H (1, a.symm x) = a.symm x at hfix
    rw [H.apply_one] at hfix
    change B (a.symm x) = a.symm x at hfix
    change a (B (a.symm x)) = x
    rw [hfix, a.apply_symm_apply]
  have hstar : StarConvex ℝ (0 : Fin 3 → ℝ) (coordinateCylinder J) :=
    (convex_coordinateCylinder J).starConvex (by intro i _; simp)
  exact ⟨C, fun _ => rfl, hCPL,
    ⟨C.relativeSupportedAlexanderHomotopy (by norm_num) hCout hstar hCrel⟩⟩

end PoincareConjecture.M76
