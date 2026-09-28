import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PeriodicPolarFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedHeightLiftImage










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞





theorem exists_saddle_nonnested_phase_ambient
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (H : (ℝ × ℝ) × ℝ → ℝ) (hH : ContDiff ℝ ∞ H)
    (hPeriod : ∀ t u s : ℝ,
      H ((t, u), s + 2 * Real.pi) = H ((t, u), s) + 2 * Real.pi)
    (hPositive : ∀ t u s : ℝ,
      0 < deriv (fun a : ℝ => H ((t, u), a)) s)
    (delta : ℝ) (hDelta : 0 < delta)
    (hInner : ∀ t u s : ℝ, u ≤ delta → H ((t, u), s) = s)
    (C : Set E2) (hC : IsCompact C)
    (hZero : ∀ x : E2, ∀ s : ℝ,
      H ((0, ‖x‖ ^ 2), s) = s)
    (hFix : ∀ t : ℝ, ∀ x : E2, x ∉ C → ∀ s : ℝ,
      H ((t, ‖x‖ ^ 2), s) = s)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hsChi : HasCompactSupport chi) (u : UnitTwoSphere) :
    ∃ (A : ℝ → D2) (G : D3),
      ContDiff ℝ ∞ (fun p : ℝ × E2 => A p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (A p.1).symm p.2) ∧
      (∀ t : ℝ, ∀ x : E2, ‖A t x‖ = ‖x‖ ∧ ‖(A t).symm x‖ = ‖x‖) ∧
      (∀ t r : ℝ, 0 ≤ r → ∀ s : ℝ,
        A t (r • J2.symm (Real.cos s, Real.sin s)) =
          r • J2.symm (Real.cos (H ((t, r ^ 2), s)),
            Real.sin (H ((t, r ^ 2), s)))) ∧
      (∀ x : E2, A 0 x = x ∧ (A 0).symm x = x) ∧
      (∀ t : ℝ, ∀ x : E2, x ∉ C → A t x = x ∧ (A t).symm x = x) ∧
      (∀ x : E2, ∀ z : ℝ,
        G ((heightPlaneCoordinates u).symm (x, z)) =
            (heightPlaneCoordinates u).symm (A (chi z) x, z) ∧
        G.symm ((heightPlaneCoordinates u).symm (x, z)) =
            (heightPlaneCoordinates u).symm ((A (chi z)).symm x, z)) ∧
      IsCompact ((heightPlaneCoordinates u).symm ''
        (C ×ˢ tsupport chi)) ∧
      tsupport (fun y : E3 => G y - y) ⊆
        (heightPlaneCoordinates u).symm '' (C ×ˢ tsupport chi) ∧
      tsupport (fun y : E3 => G.symm y - y) ⊆
        (heightPlaneCoordinates u).symm '' (C ×ˢ tsupport chi) ∧
      G '' ((heightPlaneCoordinates u).symm ''
        (⋃ z : ℝ, closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        (heightPlaneCoordinates u).symm ''
          (⋃ z : ℝ, closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
      G.symm '' ((heightPlaneCoordinates u).symm ''
        (⋃ z : ℝ, closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        (heightPlaneCoordinates u).symm ''
          (⋃ z : ℝ, closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
  obtain ⟨A, hA, hAi, hNorm, hPolar, hAfix⟩ :=
    exists_saddle_periodic_polar_family J2 hJ2 H hH hPeriod hPositive
      delta hDelta hInner
  have hzero : ∀ x : E2, A 0 x = x := by
    intro x
    exact (hAfix 0 x (hZero x)).1
  have hzeroInv : ∀ x : E2, (A 0).symm x = x := by
    intro x
    exact (hAfix 0 x (hZero x)).2
  have hfix : ∀ t : ℝ, ∀ x : E2, x ∉ C → A t x = x := by
    intro t x hx
    exact (hAfix t x (hFix t x hx)).1
  have hfixInv : ∀ t : ℝ, ∀ x : E2, x ∉ C → (A t).symm x = x := by
    intro t x hx
    exact (hAfix t x (hFix t x hx)).2
  have himage (z : ℝ) :
      A (chi z) '' (closedBall (0 : E2) 1) = closedBall 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff]
      rw [(hNorm (chi z) x).1]
      exact mem_closedBall_zero_iff.mp hx
    · intro hy
      let x := (A (chi z)).symm y
      have hx : x ∈ closedBall (0 : E2) 1 := by
        dsimp [x]
        rw [mem_closedBall_zero_iff, (hNorm (chi z) y).2]
        exact mem_closedBall_zero_iff.mp hy
      exact ⟨x, hx, by dsimp [x]; rw [(A (chi z)).apply_symm_apply]⟩
  obtain ⟨G, hG, hGc, hGs, hGsi, hGimage, hGimageInv⟩ :=
    exists_nonnested_height_lift_image A hA hzero C hC hfix chi hchi hsChi u
      (fun _ => closedBall (0 : E2) 1) (fun _ => closedBall (0 : E2) 1)
      (fun z => himage z)
  refine ⟨A, G, hA, hAi, hNorm, ?_, ?_, ?_, hG, hGc, hGs, hGsi,
    hGimage, hGimageInv⟩
  · intro t r hr s
    simpa only [Prod.smul_mk] using hPolar t r hr s
  · intro x
    exact ⟨hzero x, hzeroInv x⟩
  · intro t x hx
    exact ⟨hfix t x hx, hfixInv t x hx⟩

end PoincareConjecture.M25.Topology3D
