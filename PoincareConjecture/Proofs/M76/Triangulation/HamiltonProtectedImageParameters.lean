import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedLiftPL
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardSource
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

theorem compactified_protected_image_isFinitePL
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set E} {D P : Set V}
    (u : S ≃ₜ P) (param : E → D)
    (hparam : ∀ x : S, (param x : V) = (u x : V))
    (p : V → V) (hPfix : EqOn p id P)
    (G : D ≃ₜ D) (A : V ≃ₜ V)
    (hA : ∀ y : D, A (p y) = p (G y))
    (hf : FinitePiecewiseAffineOn (fun x => p (G (param x))) S) :
    (u.trans (A.image P)).IsFinitePL := by
  refine ⟨fun x => p (G (param x)), hf, ?_⟩
  intro x
  have hpx : (param x : V) ∈ P := (hparam x).symm ▸ (u x).property
  have h := hA (param x)
  rw [hPfix hpx, hparam x] at h
  exact h

private theorem unit_cube_three_ball :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (closedBall (0 : Fin 3 → ℝ) 1)
      (sphere (0 : Fin 3 → ℝ) 1) := by
  let c : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨f, hf, hfb⟩ := HamiltonIndexTwoStandard.source.ball.exists_cube_chart c
  apply HamiltonIndexTwoStandard.source.ball.of_homeomorph sphere_subset_closedBall
    f.symm hf.symm
  intro x
  have h := hfb (f.symm x)
  rw [f.apply_symm_apply, frontier_closedBall _ one_ne_zero] at h
  exact h.symm

theorem protected_image_three_ball
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {P B : Set V} (hBP : B ⊆ P)
    (u : closedBall (0 : Fin 3 → ℝ) 1 ≃ₜ P)
    (huB : ∀ x : closedBall (0 : Fin 3 → ℝ) 1,
      (u x : V) ∈ B ↔ (x : Fin 3 → ℝ) ∈ sphere (0 : Fin 3 → ℝ) 1)
    (A : V ≃ₜ V) (huA : (u.trans (A.image P)).IsFinitePL) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (A '' P) (A '' B) := by
  let f := u.trans (A.image P)
  apply unit_cube_three_ball.of_homeomorph (image_mono hBP) f.symm huA.symm
  intro y
  have hy : A (u (f.symm y)) = (y : V) :=
    congrArg Subtype.val (f.apply_symm_apply y)
  have hmem : (y : V) ∈ A '' B ↔ (u (f.symm y) : V) ∈ B := by
    rw [← hy]
    exact A.injective.mem_set_image
  exact hmem.trans (huB (f.symm y))

theorem protected_image_disk_pair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s t q : Set V}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (e : s ≃ₜ t) (he : e.IsFinitePL)
    (hfix : ∀ x : s, (x : V) ∈ q → (e x : V) = x) :
    IsFinitePLBallPair (ℝ × ℝ) t q := by
  have hqt : q ⊆ t := by
    intro x hx
    have hxval := (e ⟨x, hs.1 hx⟩).property
    rwa [hfix ⟨x, hs.1 hx⟩ hx] at hxval
  have hmem := e.mem_subset_iff_of_extension (Homeomorph.refl q) hs.1 hqt
    (fun x => Subtype.ext (hfix ⟨x, hs.1 x.property⟩ x.property))
  apply hs.of_homeomorph hqt e.symm he.symm
  intro y
  have h := hmem (e.symm y)
  rw [e.apply_symm_apply] at h
  exact h.symm

end PoincareConjecture.M76
