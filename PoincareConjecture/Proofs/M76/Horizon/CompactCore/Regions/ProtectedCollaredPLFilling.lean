import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.ProtectedInnerSquareFilling
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedInnerSquarePLApproximation












set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1

theorem PLDomain.exists_protected_collared_PL_filling
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hF : IsCompact F)
    (hne : F.Nonempty) (hcut : Y ∩ frontier K = F)
    (gamma : C(Q, F)) (f : C(D, Y))
    (hf : ∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (gamma u : X)) :
    ∃ (q : V2 → X) (d : C(D, Y)) (A : C(I × Q, Y)) (T : C(I × D, Y)),
      PolyhedralPLInCharts e q D ∧ MapsTo q D Y ∧
      (∀ x ∈ D, (3 / 4 : ℝ) ≤ ‖x‖ → q x ∈ interior K) ∧
      (∀ u : Q, (A (0, u) : X) = (gamma u : X)) ∧
      (∀ u : Q, A (1, u) = d ⟨u, sphere_subset_closedBall u.property⟩) ∧
      (∀ (t : I) (u : Q), 0 < (t : ℝ) → (A (t, u) : X) ∈ interior K) ∧
      (∀ x : D, T (0, x) = d x) ∧
      (∀ x : D, (T (1, x) : X) = q x) ∧
      ∀ (t : I) (x : D), (3 / 4 : ℝ) ≤ ‖(x : V2)‖ →
        (T (t, x) : X) ∈ interior K := by
  obtain ⟨H, d, _, _, _, _, hdside, A, hA0, hA1, hAside⟩ :=
    hK.exists_protected_inner_square_filling hY hF hne hcut gamma f hf
  obtain ⟨q, hq, hqY, T, hT0, hT1, hTside⟩ :=
    exists_protected_inner_square_PL_approximation e hK.compatible hK.cover
      hY isOpen_interior d hdside
  refine ⟨q, d, A, T, hq, hqY, ?_, hA0, hA1, hAside, hT0, hT1, hTside⟩
  intro x hx hnorm
  rw [← hT1 ⟨x, hx⟩]
  exact hTside 1 ⟨x, hx⟩ hnorm

end PoincareConjecture.M76
