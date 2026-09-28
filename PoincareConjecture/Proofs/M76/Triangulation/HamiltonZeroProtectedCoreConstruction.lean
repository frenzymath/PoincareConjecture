import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedCoreConstruction

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [IsEmpty ι]
  {L : Submodule ℤ (κ → ℝ)}
  {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J
local notation "C" => closedBall (0 : V) 1

theorem exists_hamiltonProtectedCoreData_zero_marked
    (h : V → E)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (hpcore : ∀ y, ‖y‖ ≤ 1 → p y = y)
    (hpiPL : LocallyPiecewiseAffineOn p.symm p.target)
    (A : V ≃ₜ V) (G : D ≃ₜ D) (hA : ∀ y : D, A (p y) = p (G y))
    (hAout : ∀ x, 2 ≤ ‖x‖ → A x = x)
    (P : Set V) (hPC : P ⊆ C) (hP0 : (0 : V) ∈ interior P)
    (i : α) (b : (Fin 3 → ℝ) →ᴬ[ℝ] E)
    (hchart : ∀ y ∈ P, latticeCoordinateProjection ι κ L y ∈ (e i).source)
    (hformula : ∀ y ∈ P, h y = b (e i (latticeCoordinateProjection ι κ L y))) :
    ∃ data : HamiltonProtectedCoreData ι κ L h e d p A,
      data.protectedRegion = P := by
  have hD : D = univ := by
    ext x
    constructor
    · exact fun _ => mem_univ x
    · intro _ j hj
      obtain ⟨i, _, _⟩ := Finset.mem_map.mp hj
      exact isEmptyElim i
  obtain ⟨Q, hQPL, hQout, hplace⟩ := exists_hamilton_zero_core_placement A hAout P hP0
  apply exists_hamiltonProtectedCoreData_of_fixed_region_marked h e d hd p hps hpiPL
    A G hA P (fun y hy => hpcore y (mem_closedBall_zero_iff.mp (hPC hy)))
    (by rw [hD]; exact subset_univ P) i b hchart hformula Q hQPL hQout ?_ hplace
  intro x hx
  simp only [hD, compl_univ, frontier_univ, union_self, mem_empty_iff_false] at hx

end PoincareConjecture.M76
