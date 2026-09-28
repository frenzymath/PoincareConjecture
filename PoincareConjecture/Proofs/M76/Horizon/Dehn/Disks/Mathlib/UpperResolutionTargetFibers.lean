import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionTubeFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.UpperResolutionSourceFibers









set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1



theorem upper_strip_target_fiber
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S A C B0 B1 : Set E} {f : E → X} {τ : C3 → X} {g : V2 → X}
    {pA pC : I01 → E}
    (s : UpperResolutionSources A C source pA pC minusArmPoint plusArmPoint
      f (τ ∘ strip (1 / 4) true) f g)
    (hτ : InjOn τ tube)
    (hfull : S ∩ f ⁻¹' (τ '' tube) = B0 ∪ B1) (hAS : A ⊆ S) (hCS : C ⊆ S)
    (hA0 : A ∩ B0 = range pA) (hA1 : A ∩ B1 = ∅)
    (hC0 : C ∩ B0 = ∅) (hC1 : C ∩ B1 = range pC)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t))
    (y : source) {z : V2} (hz : z ∈ D) :
    g z = g (s.jS y) ↔ z = s.jS y := by
  constructor
  · intro h
    have hinj := (replacement_target_injective hτ (show (1 / 4 : ℝ) ≤ 1 by norm_num)
      true).1
    have hAtube : A ∩ f ⁻¹' (τ '' tube) = range pA := by
      simpa only [union_empty] using retained_tube_preimage hfull hAS hA0 hA1
    have hCtube : C ∩ f ⁻¹' (τ '' tube) = range pC := by
      simpa only [empty_union] using retained_tube_preimage hfull hCS hC0 hC1
    have hkeepA (x : A) : g (s.jA x) = f x := s.keepA x
    have hkeepS (x : source) : g (s.jS x) = τ (strip (1 / 4) true x) := s.keepS x
    have hkeepC (x : C) : g (s.jC x) = f x := s.keepC x
    rcases s.cover.symm.subset hz with (⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩
    · rw [hkeepA, hkeepS] at h
      have hx : (x : E) ∈ A ∩ f ⁻¹' (τ '' tube) :=
        ⟨x.property, ⟨strip (1 / 4) true y,
          (mapsTo_tube (by norm_num : (1 / 4 : ℝ) ≤ 1) true).1 y.property, h.symm⟩⟩
      obtain ⟨t, ht⟩ := hAtube.subset hx
      have hy : minusArmPoint t = y := hinj (by
        change τ (strip (1 / 4) true ((t : ℝ), -1)) = τ (strip (1 / 4) true y)
        rw [(arm_endpoints (by norm_num : (1 / 4 : ℝ) < 1) (t : ℝ)).1, ← hA, ht]
        exact h)
      apply (s.left_middle_eq_iff x y).mpr
      exact ⟨t, ⟨ht.symm, hy.symm⟩,
        fun u hu ↦ minusArmPoint_injective (hu.2.symm.trans hy.symm)⟩
    · rw [hkeepS, hkeepS] at h
      exact congrArg s.jS (hinj h)
    · rw [hkeepC, hkeepS] at h
      have hx : (x : E) ∈ C ∩ f ⁻¹' (τ '' tube) :=
        ⟨x.property, ⟨strip (1 / 4) true y,
          (mapsTo_tube (by norm_num : (1 / 4 : ℝ) ≤ 1) true).1 y.property, h.symm⟩⟩
      obtain ⟨t, ht⟩ := hCtube.subset hx
      have hy : plusArmPoint t = y := hinj (by
        change τ (strip (1 / 4) true ((t : ℝ), 1)) = τ (strip (1 / 4) true y)
        rw [(arm_endpoints (by norm_num : (1 / 4 : ℝ) < 1) (t : ℝ)).2.1, ← hC, ht]
        exact h)
      apply Eq.symm
      apply (s.middle_right_eq_iff y x).mpr
      exact ⟨t, ⟨hy.symm, ht.symm⟩,
        fun u hu ↦ plusArmPoint_injective (hu.1.symm.trans hy.symm)⟩
  · rintro rfl
    rfl

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
