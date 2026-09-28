import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardPlacement
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoTarget

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexTwoStandard

local notation "V" => (Fin 3 → ℝ)
local notation "D" => coordinateCylinder ({0, 1} : Finset (Fin 3))

private theorem cylinder_inter_closedBall_subset_box :
    D ∩ closedBall (0 : V) 2 ⊆ Icc lowerBound upperBound := by
  intro x hx
  have hzero : |x 0| ≤ 1 := hx.1 0 (by simp)
  have hone : |x 1| ≤ 1 := hx.1 1 (by simp)
  have htwo : |x 2| ≤ 2 := by
    simpa only [Real.norm_eq_abs] using
      (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mp
        (mem_closedBall_zero_iff.mp hx.2) 2
  constructor
  · intro i
    fin_cases i
    · exact (abs_le.mp hzero).1
    · exact (abs_le.mp hone).1
    · exact (abs_le.mp htwo).1
  · intro i
    fin_cases i
    · exact (abs_le.mp hzero).2
    · exact (abs_le.mp hone).2
    · exact (abs_le.mp htwo).2

theorem fixes_box_exterior (A : V ≃ₜ V)
    (hAout : ∀ x : V, 2 ≤ ‖x‖ → A x = x)
    (hArel : EqOn A id (Dᶜ ∪ frontier D)) :
    EqOn A id (interior (Icc lowerBound upperBound))ᶜ := by
  intro x hx
  by_cases hn : 2 ≤ ‖x‖
  · exact hAout x hn
  by_cases hxi : x ∈ interior D
  · have hball : x ∈ ball (0 : V) 2 := mem_ball_zero_iff.mpr (lt_of_not_ge hn)
    have hint : x ∈ interior (D ∩ closedBall (0 : V) 2) := by
      rw [interior_inter]
      exact ⟨hxi, ball_subset_interior_closedBall hball⟩
    exact (hx (interior_mono cylinder_inter_closedBall_subset_box hint)).elim
  by_cases hxd : x ∈ D
  · exact hArel (Or.inr ⟨subset_closure hxd, hxi⟩)
  · exact hArel (Or.inl hxd)

theorem exists_supported_placement_in_image
    (P : Set V) (delta : Bool → Set V)
    (hPL : P ⊆ Icc lowerBound upperBound)
    (hPfront : P ∩ frontier (Icc lowerBound upperBound) = side)
    (hdP : ∀ j, delta j ⊆ P) (hdside : ∀ j, delta j ∩ side = rim j)
    (hdisjoint : Disjoint (delta false) (delta true))
    (A : V ≃ₜ V) (hAout : ∀ x : V, 2 ≤ ‖x‖ → A x = x)
    (hArel : EqOn A id (Dᶜ ∪ frontier D))
    (hball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (A '' P)
      ((side ∪ A '' delta false) ∪ A '' delta true))
    (hdisk : ∀ j, IsFinitePLBallPair (ℝ × ℝ) (A '' delta j) (rim j))
    (e : ∀ j, source.disk j ≃ₜ A '' delta j) (he : ∀ j, (e j).IsFinitePL)
    (hfix : ∀ j (x : source.disk j), (x : V) ∈ rim j → (e j x : V) = x) :
    ∃ Q : V ≃ₜ V,
      FinitePiecewiseAffineOn (Q : V → V) (closedBall (0 : V) 1) ∧
      (∀ x : V, 2 ≤ ‖x‖ → Q x = x) ∧
      EqOn Q id (Dᶜ ∪ frontier D) ∧
      MapsTo Q (closedBall (0 : V) 1) (A '' P) := by
  obtain ⟨T, hTP, hTd⟩ := exists_hamilton_indexTwo_marked_target frame source
    P delta hPL hPfront hdP hdside hdisjoint A (fixes_box_exterior A hAout hArel)
    hball hdisk
  let e' : ∀ j, source.disk j ≃ₜ T.disk j :=
    fun j => (e j).trans (Homeomorph.setCongr (hTd j).symm)
  have he' (j : Bool) : (e' j).IsFinitePL := by
    obtain ⟨f, hf, heval⟩ := he j
    exact ⟨f, hf, heval⟩
  have hfix' (j : Bool) (x : source.disk j)
      (hx : (x : V) ∈ frame.rim j) : (e' j x : V) = x := hfix j x hx
  obtain ⟨Q, hQ, hQout, hQrel, _, hplace⟩ := exists_supported_placement T e' he' hfix'
  exact ⟨Q, hQ, hQout, hQrel, fun x hx => hTP ▸ hplace hx⟩

end PoincareConjecture.M76.HamiltonIndexTwoStandard
