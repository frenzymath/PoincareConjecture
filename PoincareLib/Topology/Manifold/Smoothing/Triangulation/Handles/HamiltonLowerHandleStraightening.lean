import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLowerHandleCorrection

/-!
# The named relative rigidity input and the lower-handle correction

The actual torus rigidity, covering lift and compactification are
consumed before the protected-core diagram. Its concrete chart and
standard placement data remain explicit geometric obligations.
This is not a proof that Wall, Brown, Dehn or prime decomposition
produce those data. See Hamilton 1976, pp. 67--68 and derivation331.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
  {E α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J
local notation "C" => closedBall (0 : V) 1

/-- Relative torus rigidity supplies the actual comparison and its
bounded compactified lift. Concrete protected-chart and standard
normalization data then supply the lower-handle straightening.
The remaining geometric supplier is explicit and does not assert
PL regularity of the corrected original map. See derivation331. -/
theorem lowerHandleStraightening_of_relativeTorusRigidity
    (h : V → E)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    (hindex : Fintype.card ι + Fintype.card κ = 3) (hlower : Fintype.card ι ≤ 2)
    (rigidity : HasHamiltonRelativeTorusRigidity ι κ L e d)
    (hstandard : StandardLatticeHandleAtlas ι κ L d)
    (he : IsPLIrreducible e (latticeHandleDomain ι κ L))
    (hd : IsPLIrreducible d (latticeHandleDomain ι κ L))
    (phi : C(LatticeHandle ι κ L, LatticeHandle ι κ L))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain ι κ L phi))
    (hproper : phi ⁻¹' latticeHandleBoundary ι κ L = latticeHandleBoundary ι κ L)
    (hidentity : Nonempty ((ContinuousMap.id (LatticeHandle ι κ L)).HomotopyRel
      phi (latticeHandleBoundary ι κ L)))
    (coreData : ∀ (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L),
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain ι κ L g) →
      ∀ (G : D ≃ₜ D),
        (∀ y, ((coordinateCylinderProduct ι κ (G y)).1,
            QuotientAddGroup.mk (coordinateCylinderProduct ι κ (G y)).2) =
          g ((coordinateCylinderProduct ι κ y).1,
            QuotientAddGroup.mk (coordinateCylinderProduct ι κ y).2)) →
        (∀ y : D, (y : V) ∈ frontier D → G y = y) →
        ∀ (bound : ℝ), 0 < bound → (∀ y : D, ‖(G y : V) - y‖ ≤ bound) →
        ∀ (p : OpenPartialHomeomorph V V),
          p.source = univ → p.target = ball 0 2 →
          (∀ y, ‖y‖ ≤ 1 → p y = y) →
          LocallyPiecewiseAffineOn p p.source →
          LocallyPiecewiseAffineOn p.symm p.target →
          ∀ (A : V ≃ₜ V), (∀ y : D, A (p y) = p (G y)) →
            (∀ x, 2 ≤ ‖x‖ → A x = x) →
            (∀ x ∈ Dᶜ ∪ frontier D, A x = x) →
            Nonempty (HamiltonProtectedCoreData ι κ L h e d p A)) :
    ∃ B : V ≃ₜ V, FinitePiecewiseAffineOn (h ∘ B) C ∧
      Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id V) ⟨B, B.continuous⟩
        (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
          ∀ x ∈ Dᶜ ∪ frontier D, f x = x)) := by
  obtain ⟨g, hgPL, G, hG, hGfront, bound, hbound, hGbound,
    p, hps, hpt, hpcore, hpPL, hpiPL, A, hA, ⟨H⟩⟩ :=
    exists_compactifiedHandleComparison_of_relativeTorusRigidity
      ι κ L e d hindex hlower rigidity hstandard he hd phi hphi hproper hidentity
  have hAout (x : V) (hx : 2 ≤ ‖x‖) : A x = x := by
    have hfix := (H.prop 1).2.1 x hx
    change H (1, x) = x at hfix
    rwa [H.apply_one] at hfix
  have hArel (x : V) (hx : x ∈ Dᶜ ∪ frontier D) : A x = x := by
    have hfix := (H.prop 1).2.2 x hx
    change H (1, x) = x at hfix
    rwa [H.apply_one] at hfix
  obtain ⟨data⟩ := coreData g hgPL G hG hGfront bound hbound hGbound
    p hps hpt hpcore hpPL hpiPL A hA hAout hArel
  obtain ⟨B, _, hBPL, hBhomotopy⟩ :=
    lowerHandleStraightening_of_marked_core_comparison h e d g hgPL G hG
      p hps A hA hAout hArel data
  exact ⟨B, hBPL, hBhomotopy⟩

end PoincareMT.M76
