import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerHandleCorrection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)}
  {E α β γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J
local notation "C" => closedBall (0 : V) 1
local notation "R" => latticeHandleDomain ι κ L





theorem lowerHandleStraightening_of_protected_atlas_comparison
    (h : V → E)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (e' : γ → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (U : Set R) (hidentity : ChartwisePLOn e' e (ContinuousMap.id R) U)
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L)
    (hgPL : ChartwisePLHomeomorph e' d (latticeHandleHomeomorphInDomain ι κ L g))
    (G : D ≃ₜ D)
    (hG : ∀ y, ((coordinateCylinderProduct ι κ (G y)).1,
        QuotientAddGroup.mk (coordinateCylinderProduct ι κ (G y)).2) =
      g ((coordinateCylinderProduct ι κ y).1,
        QuotientAddGroup.mk (coordinateCylinderProduct ι κ y).2))
    (p : OpenPartialHomeomorph V V) (hps : p.source = univ)
    (A : V ≃ₜ V) (hA : ∀ y : D, A (p y) = p (G y))
    (hAoutside : ∀ x, 2 ≤ ‖x‖ → A x = x)
    (hArelative : ∀ x ∈ Dᶜ ∪ frontier D, A x = x)
    (data : HamiltonProtectedCoreData ι κ L h e d p A)
    (hprotected : ∀ (y : V) (hy : y ∈ data.protectedRegion),
      cylinderLatticeProjection ι κ L ⟨y, data.protected_in_handle hy⟩ ∈ U) :
    ∃ B : V ≃ₜ V,
      (∀ x, B x = A.symm (data.normalization x)) ∧
      FinitePiecewiseAffineOn (h ∘ B) C ∧
      Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id V) ⟨B, B.continuous⟩
        (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
          ∀ x ∈ Dᶜ ∪ frontier D, f x = x)) := by
  let r := latticeHandleHomeomorphInDomain ι κ L g
  have hpre : MapsTo (A.symm ∘ data.normalization) C data.protectedRegion := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := data.placement hx
    change A.symm (data.normalization x) ∈ data.protectedRegion
    rw [← heq, A.symm_apply_apply]
    exact hy
  have hquot (y : D) :
      r (cylinderLatticeProjection ι κ L y) = cylinderLatticeProjection ι κ L (G y) := by
    apply (latticeHandleDomainEquiv ι κ L).injective
    exact (hG y).symm
  have hpoint (x : V) (hx : x ∈ C) :
      r.symm (data.quotient x) = cylinderLatticeProjection ι κ L
        ⟨A.symm (data.normalization x), data.protected_in_handle (hpre hx)⟩ := by
    let y : D := ⟨A.symm (data.normalization x), data.protected_in_handle (hpre hx)⟩
    have hpy : p y = (y : V) := data.protected_fixed (hpre hx)
    have hpGy : p (G y) = data.normalization x := by
      rw [← hA y, hpy]
      exact A.apply_symm_apply _
    have hpinv : p.symm (data.normalization x) = (G y : V) := by
      rw [← hpGy]
      exact p.left_inv (hps.symm ▸ mem_univ (G y : V))
    have hqy : data.quotient x = cylinderLatticeProjection ι κ L (G y) := by
      apply Subtype.ext
      rw [data.quotient_formula x hx, hpinv]
      rfl
    rw [hqy, ← hquot y, r.symm_apply_apply]
  obtain ⟨K, hK, hKC, _⟩ := data.normalization_PL
  let q' : V → R := fun x => r.symm (data.quotient x)
  have hq' : ContinuousOn q' K.space :=
    r.symm.continuous.comp_continuousOn (by simpa only [hKC] using data.quotient_continuous)
  have hq'PL : PolyhedralPLInCharts e'
      (fun x => (q' x : LatticeHandleAmbient ι κ L)) K.space :=
    hgPL.2.polyhedralPLInCharts_comp K hK data.quotient
      (by simpa only [hKC] using data.quotient_continuous)
      (by simpa only [hKC] using data.quotient_PL) (mapsTo_univ _ _)
  have hq'U : MapsTo q' K.space U := by
    intro x hx
    dsimp only [q']
    rw [hpoint x (hKC ▸ hx)]
    exact hprotected _ (hpre (hKC ▸ hx))
  have hformula : FinitePiecewiseAffineOn
      (fun x => e data.sourceIndex (r.symm (data.quotient x))) C := by
    rw [← hKC]
    apply hidentity.finitePiecewiseAffineOn_fixed_chart K hK q' hq' hq'PL hq'U
      data.sourceIndex
    intro x hx
    change (r.symm (data.quotient x) : LatticeHandleAmbient ι κ L) ∈
      (e data.sourceIndex).source
    rw [hpoint x (hKC ▸ hx)]
    exact data.chart_contains _ (hpre (hKC ▸ hx))
  let B := data.normalization.trans A.symm
  have hBPL : FinitePiecewiseAffineOn (h ∘ B) C :=
    (hformula.postcomp data.originalCoordinates).congr (by
      intro x hx
      change data.originalCoordinates (e data.sourceIndex (r.symm (data.quotient x))) =
        h (A.symm (data.normalization x))
      rw [hpoint x hx]
      exact (data.original_formula _ (hpre hx)).symm)
  have hBout (x : V) (hx : 2 ≤ ‖x‖) : B x = x := by
    apply A.injective
    change A (A.symm (data.normalization x)) = A x
    rw [A.apply_symm_apply, data.normalization_outside x hx, hAoutside x hx]
  have hBrel (x : V) (hx : x ∈ Dᶜ ∪ frontier D) : B x = x := by
    apply A.injective
    change A (A.symm (data.normalization x)) = A x
    rw [A.apply_symm_apply, data.normalization_relative x hx, hArelative x hx]
  have hstar : StarConvex ℝ (0 : V) D :=
    (convex_coordinateCylinder J).starConvex (by intro i _; simp)
  exact ⟨B, fun _ => rfl, hBPL,
    ⟨B.relativeSupportedAlexanderHomotopy (by norm_num) hBout hstar
      (fun x hx => hBrel x (Or.inl hx))⟩⟩

end PoincareConjecture.M76
