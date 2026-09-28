import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionTubeFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionSourceFibers

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

theorem alternate_strip_target_fibers
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S A M C B0 B1 : Set E} {f : E → X} {τ : C3 → X} {g : V2 → X}
    {pA pL pR pC : I01 → E}
    (s : AlternateResolutionSources A M C source pA pL pR pC minusArmPoint plusArmPoint
      f (τ ∘ alternate (1 / 4) false) f (τ ∘ alternate (1 / 4) true) f g)
    (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = B0 ∪ B1)
    (hAS : A ⊆ S) (hMS : M ⊆ S) (hCS : C ⊆ S)
    (hA0 : A ∩ B0 = range pA) (hA1 : A ∩ B1 = ∅)
    (hM0 : M ∩ B0 = range pR) (hM1 : M ∩ B1 = range pL)
    (hC0 : C ∩ B0 = ∅) (hC1 : C ∩ B1 = range pC)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t))
    (y : source) {z : V2} (hz : z ∈ D) :
    (g z = g (s.jL y) ↔ z = s.jL y) ∧ (g z = g (s.jR y) ↔ z = s.jR y) := by
  have hb : (1 / 4 : ℝ) < 1 := by norm_num
  have hinjL := (replacement_target_injective hτ hb.le false).2
  have hinjR := (replacement_target_injective hτ hb.le true).2
  have hsep := alternate_target_disjoint hτ (by norm_num : (0 : ℝ) < 1 / 4) hb.le
  have hmL (y : source) : alternate (1 / 4) false y ∈ tube :=
    (mapsTo_tube hb.le false).2 y.property
  have hmR (y : source) : alternate (1 / 4) true y ∈ tube :=
    (mapsTo_tube hb.le true).2 y.property
  have hAtube : A ∩ f ⁻¹' (τ '' tube) = range pA := by
    simpa only [union_empty] using retained_tube_preimage hfull hAS hA0 hA1
  have hCtube : C ∩ f ⁻¹' (τ '' tube) = range pC := by
    simpa only [empty_union] using retained_tube_preimage hfull hCS hC0 hC1
  have hMtube : M ∩ f ⁻¹' (τ '' tube) = range pL ∪ range pR := by
    simpa only [union_comm] using retained_tube_preimage hfull hMS hM0 hM1
  have hAc (t : I01) : f (pA t) = τ (alternate (1 / 4) false (plusArmPoint t)) := by
    simpa only [plusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.2] using hA t
  have hLc (t : I01) : f (pL t) = τ (alternate (1 / 4) false (minusArmPoint t)) := by
    simpa only [minusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.1] using hL t
  have hRc (t : I01) : f (pR t) = τ (alternate (1 / 4) true (minusArmPoint t)) := by
    simpa only [minusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.1] using hR t
  have hCc (t : I01) : f (pC t) = τ (alternate (1 / 4) true (plusArmPoint t)) := by
    simpa only [plusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.1] using hC t
  have hAL := retained_replacement_fiber hAtube hmL hinjL plusArmPoint_injective hAc
  have hML := retained_two_replacement_fiber
    (r' := fun y : source ↦ alternate (1 / 4) true y) hMtube hmL hinjL
    minusArmPoint_injective hLc hRc hsep
  have hMR := retained_two_replacement_fiber
    (r' := fun y : source ↦ alternate (1 / 4) false y)
    (hMtube.trans (union_comm _ _)) hmR hinjR
    minusArmPoint_injective hRc hLc hsep.symm
  have hCR := retained_replacement_fiber hCtube hmR hinjR plusArmPoint_injective hCc
  have hAR := retained_opposite_replacement_ne
    (r' := fun y : source ↦ alternate (1 / 4) false y) hAtube hmR hAc hsep.symm
  have hCL := retained_opposite_replacement_ne
    (r' := fun y : source ↦ alternate (1 / 4) true y) hCtube hmL hCc hsep
  have hkeepA (x : A) : g (s.jA x) = f x := s.keepA x
  have hkeepL (x : source) : g (s.jL x) = τ (alternate (1 / 4) false x) := s.keepL x
  have hkeepM (x : M) : g (s.jM x) = f x := s.keepM x
  have hkeepR (x : source) : g (s.jR x) = τ (alternate (1 / 4) true x) := s.keepR x
  have hkeepC (x : C) : g (s.jC x) = f x := s.keepC x
  constructor
  · constructor
    · intro h
      rcases s.cover.symm.subset hz with
        ((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
      · rw [hkeepA, hkeepL] at h
        exact (s.A_left_eq_iff x y).mpr ((hAL x y).mp h)
      · rw [hkeepL, hkeepL] at h
        exact congrArg s.jL (hinjL h)
      · rw [hkeepM, hkeepL] at h
        apply Eq.symm
        apply (s.left_middle_eq_iff y x).mpr
        simpa only [and_comm] using (hML x y).mp h
      · rw [hkeepR, hkeepL] at h
        exact False.elim (disjoint_left.mp hsep ⟨y, rfl⟩ ⟨x, h⟩)
      · rw [hkeepC, hkeepL] at h
        exact False.elim (hCL x y h)
    · rintro rfl
      rfl
  · constructor
    · intro h
      rcases s.cover.symm.subset hz with
        ((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
      · rw [hkeepA, hkeepR] at h
        exact False.elim (hAR x y h)
      · rw [hkeepL, hkeepR] at h
        exact False.elim (disjoint_left.mp hsep ⟨x, h⟩ ⟨y, rfl⟩)
      · rw [hkeepM, hkeepR] at h
        exact (s.middle_right_eq_iff x y).mpr ((hMR x y).mp h)
      · rw [hkeepR, hkeepR] at h
        exact congrArg s.jR (hinjR h)
      · rw [hkeepC, hkeepR] at h
        apply Eq.symm
        apply (s.right_C_eq_iff y x).mpr
        simpa only [and_comm] using (hCR x y).mp h
    · rintro rfl
      rfl

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
