import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroCorePlacement











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

private theorem polyhedralPLInCharts_congr
    {E F X β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
    {d : β → OpenPartialHomeomorph X F} {f g : E → X} {S : Set E}
    (hf : PolyhedralPLInCharts d f S) (heq : EqOn f g S) :
    PolyhedralPLInCharts d g S := by
  refine ⟨hf.continuousOn.congr heq.symm, ?_⟩
  intro x
  obtain ⟨i, K, U, hK, hKS, hU, hxU, hUK, hfK, hcoords⟩ := hf.coordinates x
  refine ⟨i, K, U, hK, hKS, hU, hxU, hUK, ?_, ?_⟩
  · intro y hy
    rw [← heq (hKS hy)]
    exact hfK hy
  · exact hcoords.congr (fun y hy => congrArg (d i) (heq (hKS hy)))

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)}
  {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J
local notation "C" => closedBall (0 : V) 1
local notation "R" => latticeHandleDomain ι κ L






theorem exists_hamiltonProtectedCoreData_of_fixed_region_marked
    (h : V → E)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (hpiPL : LocallyPiecewiseAffineOn p.symm p.target)
    (A : V ≃ₜ V) (G : D ≃ₜ D) (hA : ∀ y : D, A (p y) = p (G y))
    (P : Set V) (hPfixed : EqOn p id P) (hPD : P ⊆ D)
    (i : α) (b : (Fin 3 → ℝ) →ᴬ[ℝ] E)
    (hchart : ∀ y ∈ P, latticeCoordinateProjection ι κ L y ∈ (e i).source)
    (hformula : ∀ y ∈ P, h y = b (e i (latticeCoordinateProjection ι κ L y)))
    (Q : V ≃ₜ V) (hQPL : FinitePiecewiseAffineOn Q C)
    (hQout : ∀ x, 2 ≤ ‖x‖ → Q x = x)
    (hQrel : ∀ x ∈ Dᶜ ∪ frontier D, Q x = x)
    (hplace : MapsTo Q C (A '' P)) :
    ∃ data : HamiltonProtectedCoreData ι κ L h e d p A,
      data.protectedRegion = P := by
  classical
  have hpre (x : V) (hx : x ∈ C) : ∃ y : D,
      p (G y) = Q x ∧ p.symm (Q x) = (G y : V) := by
    obtain ⟨y, hy, heq⟩ := hplace hx
    let yD : D := ⟨y, hPD hy⟩
    have hpy : p yD = y := hPfixed hy
    have hGQ : p (G yD) = Q x := by
      rw [← hA yD, hpy]
      exact heq
    refine ⟨yD, hGQ, ?_⟩
    rw [← hGQ]
    exact p.left_inv (hps.symm ▸ mem_univ (G yD : V))
  have hQt : MapsTo Q C p.target := by
    intro x hx
    obtain ⟨y, hGy, _⟩ := hpre x hx
    rw [← hGy]
    exact p.mapsTo (hps.symm ▸ mem_univ (G y : V))
  have hrawPL := hd.polyhedralPL_inverse_compression p hpiPL Q hQPL hQt
  have hrawR (x : V) (hx : x ∈ C) :
      latticeCoordinateProjection ι κ L (p.symm (Q x)) ∈ R := by
    obtain ⟨y, _, hy⟩ := hpre x hx
    rw [hy]
    exact (cylinderLatticeProjection ι κ L (G y)).property
  let z : R := cylinderLatticeProjection ι κ L ⟨0, by intro j _; simp⟩
  let q : V → R := fun x =>
    if hx : latticeCoordinateProjection ι κ L (p.symm (Q x)) ∈ R then
      ⟨latticeCoordinateProjection ι κ L (p.symm (Q x)), hx⟩ else z
  have hq (x : V) (hx : x ∈ C) :
      (q x : LatticeHandleAmbient ι κ L) =
        latticeCoordinateProjection ι κ L (p.symm (Q x)) := by
    simp only [q, dif_pos (hrawR x hx)]
  have hqPL : PolyhedralPLInCharts d
      (fun x => (q x : LatticeHandleAmbient ι κ L)) C :=
    polyhedralPLInCharts_congr hrawPL (fun x hx => (hq x hx).symm)
  have hqcont : ContinuousOn q C :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
  exact ⟨{
    protectedRegion := P
    protected_fixed := hPfixed
    protected_in_handle := hPD
    sourceIndex := i
    originalCoordinates := b
    chart_contains := hchart
    original_formula := hformula
    normalization := Q
    normalization_PL := hQPL
    normalization_outside := hQout
    normalization_relative := hQrel
    placement := hplace
    quotient := q
    quotient_continuous := hqcont
    quotient_formula := hq
    quotient_PL := hqPL
  }, rfl⟩




theorem exists_hamiltonProtectedCoreData_of_fixed_region
    (h : V → E)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (hpiPL : LocallyPiecewiseAffineOn p.symm p.target)
    (A : V ≃ₜ V) (G : D ≃ₜ D) (hA : ∀ y : D, A (p y) = p (G y))
    (P : Set V) (hPfixed : EqOn p id P) (hPD : P ⊆ D)
    (i : α) (b : (Fin 3 → ℝ) →ᴬ[ℝ] E)
    (hchart : ∀ y ∈ P, latticeCoordinateProjection ι κ L y ∈ (e i).source)
    (hformula : ∀ y ∈ P, h y = b (e i (latticeCoordinateProjection ι κ L y)))
    (Q : V ≃ₜ V) (hQPL : FinitePiecewiseAffineOn Q C)
    (hQout : ∀ x, 2 ≤ ‖x‖ → Q x = x)
    (hQrel : ∀ x ∈ Dᶜ ∪ frontier D, Q x = x)
    (hplace : MapsTo Q C (A '' P)) :
    Nonempty (HamiltonProtectedCoreData ι κ L h e d p A) := by
  obtain ⟨data, _⟩ := exists_hamiltonProtectedCoreData_of_fixed_region_marked
    h e d hd p hps hpiPL A G hA P hPfixed hPD i b hchart hformula
      Q hQPL hQout hQrel hplace
  exact ⟨data⟩




theorem exists_hamiltonProtectedCoreData
    (h : V → E)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (hpcore : ∀ y, ‖y‖ ≤ 1 → p y = y)
    (hpiPL : LocallyPiecewiseAffineOn p.symm p.target)
    (A : V ≃ₜ V) (G : D ≃ₜ D) (hA : ∀ y : D, A (p y) = p (G y))
    (P : Set V) (hPC : P ⊆ C) (hPD : P ⊆ D)
    (i : α) (b : (Fin 3 → ℝ) →ᴬ[ℝ] E)
    (hchart : ∀ y ∈ P, latticeCoordinateProjection ι κ L y ∈ (e i).source)
    (hformula : ∀ y ∈ P, h y = b (e i (latticeCoordinateProjection ι κ L y)))
    (Q : V ≃ₜ V) (hQPL : FinitePiecewiseAffineOn Q C)
    (hQout : ∀ x, 2 ≤ ‖x‖ → Q x = x)
    (hQrel : ∀ x ∈ Dᶜ ∪ frontier D, Q x = x)
    (hplace : MapsTo Q C (A '' P)) :
    Nonempty (HamiltonProtectedCoreData ι κ L h e d p A) := by
  apply exists_hamiltonProtectedCoreData_of_fixed_region h e d hd p hps hpiPL
    A G hA P ?_ hPD i b hchart hformula Q hQPL hQout hQrel hplace
  intro y hy
  exact hpcore y (mem_closedBall_zero_iff.mp (hPC hy))





theorem exists_hamiltonProtectedCoreData_zero [IsEmpty ι]
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
    Nonempty (HamiltonProtectedCoreData ι κ L h e d p A) := by
  have hD : D = univ := by
    ext x
    constructor
    · exact fun _ => mem_univ x
    · intro _ j hj
      obtain ⟨i, _, _⟩ := Finset.mem_map.mp hj
      exact isEmptyElim i
  obtain ⟨Q, hQPL, hQout, hplace⟩ := exists_hamilton_zero_core_placement A hAout P hP0
  apply exists_hamiltonProtectedCoreData h e d hd p hps hpcore hpiPL A G hA P hPC
    (by rw [hD]; exact subset_univ P) i b hchart hformula Q hQPL hQout ?_ hplace
  intro x hx
  simp only [hD, compl_univ, frontier_univ, union_self, mem_empty_iff_false] at hx

end PoincareConjecture.M76
