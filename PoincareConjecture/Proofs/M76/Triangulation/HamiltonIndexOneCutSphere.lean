import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedRegionRecognition
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem isFinitePLBallPair_of_compact_spherical_frontier
    (hdim : Module.finrank ℝ E = 3) {R : Set E}
    (hR : IsCompact R) (hne : (interior R).Nonempty)
    {C : Set F} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hCne : (interior C).Nonempty) (hdimC : Module.finrank ℝ F = 3)
    (e : frontier R ≃ₜ frontier C) (he : e.IsFinitePL) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) R (frontier R) := by
  obtain ⟨J, hJ, hJcv, hRJ⟩ := hR.exists_finite_convex_neighborhood
  have hJne : (interior J.space).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hRJ (interior_subset hx)⟩
  have hregions := he.hasAlexanderRegionBalls hC hcv hCne hdimC hdim
    (J.isCompact_space_of_finite hJ) hJcv hJne
    (hR.isClosed.frontier_subset.trans hRJ) J hJ rfl
  exact hasAlexanderRegionBalls_identifies_closed_region
    hregions hR.isClosed hne rfl hRJ

namespace HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

omit [FiniteDimensional ℝ E] in




theorem exists_capped_annulus_frontier_map {A B : Set E}
    {a b : ℝ} (hab : a < b)
    (side : (Q2 ×ˢ Icc a b) ≃ₜ A)
    (caps : (D2 ×ˢ ({a, b} : Set ℝ)) ≃ₜ B)
    (hside : side.IsFinitePL) (hcaps : caps.IsFinitePL)
    (hoverlap : ∀ x : Q2 ×ˢ Icc a b,
      (x : V2 × ℝ).2 ∈ ({a, b} : Set ℝ) ↔ (side x : E) ∈ B)
    (hagree : ∀ (x : V2 × ℝ) (hs : x ∈ Q2 ×ˢ Icc a b)
      (hc : x ∈ D2 ×ˢ ({a, b} : Set ℝ)),
      (side ⟨x, hs⟩ : E) = caps ⟨x, hc⟩) :
    ∃ H : frontier (D2 ×ˢ Icc a b) ≃ₜ (A ∪ B : Set E),
      H.IsFinitePL ∧
      (∀ (x : Q2 ×ˢ Icc a b) (hx : (x : V2 × ℝ) ∈ frontier (D2 ×ˢ Icc a b)),
        (H ⟨x, hx⟩ : E) = side x) ∧
      ∀ (x : D2 ×ˢ ({a, b} : Set ℝ))
        (hx : (x : V2 × ℝ) ∈ frontier (D2 ×ˢ Icc a b)),
        (H ⟨x, hx⟩ : E) = caps x := by
  have hfront : frontier (D2 ×ˢ Icc a b) =
      (Q2 ×ˢ Icc a b) ∪ (D2 ×ˢ ({a, b} : Set ℝ)) := by
    rw [frontier_prod_eq, isClosed_closedBall.closure_eq, isClosed_Icc.closure_eq,
      frontier_closedBall _ one_ne_zero, frontier_Icc hab.le, union_comm]
  have hinter (x : Q2 ×ˢ Icc a b) :
      (x : V2 × ℝ) ∈ D2 ×ˢ ({a, b} : Set ℝ) ↔ (side x : E) ∈ B := by
    change ((x : V2 × ℝ).1 ∈ D2 ∧ (x : V2 × ℝ).2 ∈ ({a, b} : Set ℝ)) ↔ _
    exact (and_iff_right (sphere_subset_closedBall x.property.1)).trans (hoverlap x)
  obtain ⟨H, hH, hHs, hHc⟩ :=
    Homeomorph.exists_union_finitePL side caps hside hcaps hinter hagree
  refine ⟨(Homeomorph.setCongr hfront).trans H, hH.setCongr hfront.symm rfl, ?_, ?_⟩
  · intro x hx
    exact hHs x
  · intro x hx
    exact hHc x





theorem isFinitePLBallPair_of_capped_annulus_frontier
    (hdim : Module.finrank ℝ E = 3) {R A B : Set E}
    (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hfront : frontier R = A ∪ B) {a b : ℝ} (hab : a < b)
    (side : (Q2 ×ˢ Icc a b) ≃ₜ A)
    (caps : (D2 ×ˢ ({a, b} : Set ℝ)) ≃ₜ B)
    (hside : side.IsFinitePL) (hcaps : caps.IsFinitePL)
    (hoverlap : ∀ x : Q2 ×ˢ Icc a b,
      (x : V2 × ℝ).2 ∈ ({a, b} : Set ℝ) ↔ (side x : E) ∈ B)
    (hagree : ∀ (x : V2 × ℝ) (hs : x ∈ Q2 ×ˢ Icc a b)
      (hc : x ∈ D2 ×ˢ ({a, b} : Set ℝ)),
      (side ⟨x, hs⟩ : E) = caps ⟨x, hc⟩) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) R (frontier R) := by
  obtain ⟨H, hH, _, _⟩ := exists_capped_annulus_frontier_map hab side caps
    hside hcaps hoverlap hagree
  let e : frontier R ≃ₜ frontier (D2 ×ˢ Icc a b) :=
    (Homeomorph.setCongr hfront).trans H.symm
  have he : e.IsFinitePL := by
    obtain ⟨f, hf, hfeq⟩ := hH.symm
    refine ⟨f, ?_, ?_⟩
    · rw [hfront]
      exact hf
    · intro x
      exact hfeq ((Homeomorph.setCongr hfront) x)
  have hmodelne : (interior (D2 ×ˢ Icc a b)).Nonempty := by
    rw [interior_prod_eq, interior_closedBall _ one_ne_zero, interior_Icc]
    obtain ⟨t, hat, htb⟩ := exists_between hab
    exact ⟨(0, t), mem_ball_self zero_lt_one, hat, htb⟩
  have hmodeldim : Module.finrank ℝ (V2 × ℝ) = 3 := by simp [Module.finrank_prod]
  exact isFinitePLBallPair_of_compact_spherical_frontier (E := E) (F := V2 × ℝ)
    hdim hR hne ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc)
    ((convex_closedBall (0 : V2) 1).prod (convex_Icc a b)) hmodelne hmodeldim e he

end HamiltonIndexOne
end PoincareConjecture.M76
