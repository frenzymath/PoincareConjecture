import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Arcs.SquareInversion

noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.PlaneArcs

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem exterior_square_crossing {r : Real} (hr : 0 < r)
    (α β : Real → E2)
    (hα : ContinuousOn α (Icc (0 : Real) 1))
    (hβ : ContinuousOn β (Icc (0 : Real) 1))
    (hαout : ∀ t ∈ Icc (0 : Real) 1, r ≤ squareGauge (α t))
    (hβout : ∀ t ∈ Icc (0 : Real) 1, r ≤ squareGauge (β t))
    (hαend : squareGauge (α 0) = r ∧ squareGauge (α 1) = r)
    (hβend : squareGauge (β 0) = r ∧ squareGauge (β 1) = r)
    (hα0 : α 0 0 = -r) (hα1 : α 1 0 = r)
    (hβ0 : β 0 1 = -r) (hβ1 : β 1 1 = r) :
    ∃ s ∈ Icc (0 : Real) 1, ∃ t ∈ Icc (0 : Real) 1, α s = β t := by
  let θ : Real → Real := fun t => (t + 1) / 2
  have hθ : Continuous θ := (continuous_id.add continuous_const).div_const 2
  have hθI : MapsTo θ (Icc (-1 : Real) 1) (Icc (0 : Real) 1) := by
    intro t ht
    dsimp [θ]
    constructor <;> linarith [ht.1, ht.2]
  let A : Real → E2 := fun t => squareInversion r (α (θ t))
  let B : Real → E2 := fun t => squareInversion r (β (θ t))
  have hA : ContinuousOn A (Icc (-1 : Real) 1) :=
    ((continuousOn_squareInversion hr).comp hα hαout).comp hθ.continuousOn hθI
  have hB : ContinuousOn B (Icc (-1 : Real) 1) :=
    ((continuousOn_squareInversion hr).comp hβ hβout).comp hθ.continuousOn hθI
  have hAE : ∀ t ∈ Icc (-1 : Real) 1,
      A t 0 ∈ Icc (-r) r ∧ A t 1 ∈ Icc (-r) r := by
    intro t ht
    have hh := squareInversion_mem_square hr (hαout _ (hθI ht))
    exact ⟨abs_le.mp hh.1, abs_le.mp hh.2⟩
  have hBE : ∀ t ∈ Icc (-1 : Real) 1,
      B t 0 ∈ Icc (-r) r ∧ B t 1 ∈ Icc (-r) r := by
    intro t ht
    have hh := squareInversion_mem_square hr (hβout _ (hθI ht))
    exact ⟨abs_le.mp hh.1, abs_le.mp hh.2⟩
  have hA0 : A (-1) 0 = -r := by
    simpa [A, θ, squareInversion_fixed hr hαend.1] using hα0
  have hA1 : A 1 0 = r := by
    simpa [A, θ, squareInversion_fixed hr hαend.2] using hα1
  have hB0 : B (-1) 1 = -r := by
    simpa [B, θ, squareInversion_fixed hr hβend.1] using hβ0
  have hB1 : B 1 1 = r := by
    simpa [B, θ, squareInversion_fixed hr hβend.2] using hβ1
  obtain ⟨s, hs, t, ht, heq⟩ := Poincare.Topology.Plane.Jordan.crossing
    Poincare.Topology.Plane.Jordan.Brouwer.brouwerFPT
      (by linarith : -r ≤ r) (by linarith : -r ≤ r)
      A B hA hB hAE hBE hA0 hA1 hB0 hB1
  exact ⟨θ s, hθI hs, θ t, hθI ht,
    squareInversion_injOn hr (hr.trans_le (hαout _ (hθI hs)))
      (hr.trans_le (hβout _ (hθI ht))) heq⟩

def squareCorner (r : Real) (i : Fin 2 × Fin 2) : E2 :=
  WithLp.toLp 2 ![if i.1 = 0 then r else -r, if i.2 = 0 then r else -r]

theorem squareGauge_corner {r : Real} (hr : 0 < r) (i : Fin 2 × Fin 2) :
    squareGauge (squareCorner r i) = r := by
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [squareGauge, squareCorner, abs_of_pos hr]

theorem not_disjoint_exterior_opposite_corners {r : Real} (hr : 0 < r)
    (α β : Real → E2)
    (hα : ContinuousOn α (Icc (0 : Real) 1))
    (hβ : ContinuousOn β (Icc (0 : Real) 1))
    (hαout : ∀ t ∈ Icc (0 : Real) 1, r ≤ squareGauge (α t))
    (hβout : ∀ t ∈ Icc (0 : Real) 1, r ≤ squareGauge (β t))
    (hα0 : α 0 = squareCorner r (1, 1)) (hα1 : α 1 = squareCorner r (0, 0))
    (hβ0 : β 0 = squareCorner r (0, 1)) (hβ1 : β 1 = squareCorner r (1, 0)) :
    ¬ Disjoint (α '' Icc (0 : Real) 1) (β '' Icc (0 : Real) 1) := by
  obtain ⟨s, hs, t, ht, heq⟩ := exterior_square_crossing hr α β hα hβ hαout hβout
    (by simp [hα0, hα1, squareGauge_corner hr])
    (by simp [hβ0, hβ1, squareGauge_corner hr])
    (by simp [hα0, squareCorner]) (by simp [hα1, squareCorner])
    (by simp [hβ0, squareCorner]) (by simp [hβ1, squareCorner])
  intro hd
  exact disjoint_left.mp hd ⟨s, hs, rfl⟩ ⟨t, ht, heq.symm⟩

end Poincare.Manifold.Schoenflies.PlaneArcs
