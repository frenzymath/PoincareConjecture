import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.ClosedBallIsotopy

set_option autoImplicit false

open Set Geometry Metric

namespace Homeomorph

variable {ι : Type*} [Fintype ι]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_finitePL_cube_straightening {t b : Set E}
    (h : closedBall (0 : ι → ℝ) 1 ≃ₜ t) (ht : IsFinitePLBallPair F t b)
    (eb : sphere (0 : ι → ℝ) 1 ≃ₜ b) (heb : eb.IsFinitePL)
    (hboundary : ∀ x : sphere (0 : ι → ℝ) 1,
      h ⟨x, sphere_subset_closedBall x.property⟩ = ⟨eb x, ht.1 (eb x).property⟩) :
    ∃ g : closedBall (0 : ι → ℝ) 1 ≃ₜ t, g.IsFinitePL ∧
      (∀ x : sphere (0 : ι → ℝ) 1,
        g ⟨x, sphere_subset_closedBall x.property⟩ =
          h ⟨x, sphere_subset_closedBall x.property⟩) ∧
      ∃ C : (ι → ℝ) ≃ₜ (ι → ℝ),
        (∀ x : closedBall (0 : ι → ℝ) 1, C x = (h.symm (g x) : ι → ℝ)) ∧
        (∀ x, 1 ≤ ‖x‖ → C x = x) ∧
        Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id (ι → ℝ))
          ⟨C, C.continuous⟩ (fun f => IsHomeomorph f ∧ ∀ x, 1 ≤ ‖x‖ → f x = x)) := by
  obtain ⟨g, hg, hgb, _⟩ := isFinitePLBallPair_unit_cube.exists_extension ht eb heb
  have hgh (x : sphere (0 : ι → ℝ) 1) :
      g ⟨x, sphere_subset_closedBall x.property⟩ =
        h ⟨x, sphere_subset_closedBall x.property⟩ :=
    (hgb x).trans (hboundary x).symm
  let e := g.trans h.symm
  have he (x : closedBall (0 : ι → ℝ) 1) (hx : ‖(x : ι → ℝ)‖ = 1) : e x = x := by
    let xb : sphere (0 : ι → ℝ) 1 := ⟨x, by simpa only [mem_sphere, dist_zero_right] using hx⟩
    have hxg : g x = h x := hgh xb
    change h.symm (g x) = x
    rw [hxg, h.symm_apply_apply]
  let C := e.closedBallExtension he
  refine ⟨g, hg, hgh, C, ?_, e.closedBallExtension_fixed_outside he, ?_⟩
  · intro x
    exact e.closedBallExtension_apply_mem he x.property
  · exact ⟨e.closedBallAlexanderHomotopy zero_le_one he⟩

end Homeomorph
