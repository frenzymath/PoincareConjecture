import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonTorusRigidity
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Coverings.BoundedHandleLift
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.PLHandleCompactification

/-!
# The actual relative rigidity, bounded lift and compactification chain

Hamilton's named relative torus-rigidity input supplies the actual
comparison and its whole-boundary homotopy. The checked covering lift
and core-fixing PL compression then produce the supported ambient
isotopy in the original marked coordinates. This does not assert
PL straightening on the prescribed core: its structure comparison
and inverse-core placement are separate remaining obligations.
See Hamilton 1976, pp. 67--68 and M76 derivations 319--320.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
  {α β : Type*}

local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J

/-- The lower-handle comparison obtained from the named relative
rigidity input has an actual bounded lift and supported compactified
isotopy. All quotient and boundary equations use the same original
lattice. The source approximation and both irreducibility assertions
remain explicit geometric hypotheses. See Hamilton pp. 67--68 and
M76 derivation319. -/
theorem exists_compactifiedHandleComparison_of_relativeTorusRigidity
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
      phi (latticeHandleBoundary ι κ L))) :
    ∃ g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain ι κ L g) ∧
      ∃ G : D ≃ₜ D,
        (∀ x, ((coordinateCylinderProduct ι κ (G x)).1,
            QuotientAddGroup.mk (coordinateCylinderProduct ι κ (G x)).2) =
          g ((coordinateCylinderProduct ι κ x).1,
            QuotientAddGroup.mk (coordinateCylinderProduct ι κ x).2)) ∧
        (∀ x : D, (x : (ι ⊕ κ) → ℝ) ∈ frontier D → G x = x) ∧
        ∃ C > 0, (∀ x : D, ‖(G x : (ι ⊕ κ) → ℝ) - x‖ ≤ C) ∧
          ∃ p : OpenPartialHomeomorph ((ι ⊕ κ) → ℝ) ((ι ⊕ κ) → ℝ),
            p.source = univ ∧ p.target = ball 0 2 ∧
            (∀ x, ‖x‖ ≤ 1 → p x = x) ∧
            LocallyPiecewiseAffineOn p p.source ∧
            LocallyPiecewiseAffineOn p.symm p.target ∧
            ∃ A : ((ι ⊕ κ) → ℝ) ≃ₜ ((ι ⊕ κ) → ℝ),
              (∀ x : D, A (p x) = p (G x)) ∧
              Nonempty (ContinuousMap.HomotopyWith
                (ContinuousMap.id ((ι ⊕ κ) → ℝ)) ⟨A, A.continuous⟩
                (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
                  ∀ x ∈ Dᶜ ∪ frontier D, f x = x)) := by
  obtain ⟨g, hgPL, _, ⟨Hg⟩⟩ :=
    rigidity hindex hlower hstandard he hd phi hphi hproper hidentity
  obtain ⟨G, hGquotient, hGfrontier, C, hC, hGbound⟩ :=
    exists_boundedHandleLift ι κ L g Hg
  obtain ⟨p, hps, hpt, hpcore, hpPL, hpiPL, hcompact⟩ :=
    exists_plHandleCompactification (ι ⊕ κ) J
  obtain ⟨A, hA, hhomotopy⟩ := hcompact G C hC.le hGbound hGfrontier
  exact ⟨g, hgPL, G, hGquotient, hGfrontier, C, hC, hGbound,
    p, hps, hpt, hpcore, hpPL, hpiPL, A, hA, hhomotopy⟩

end PoincareMT.M76
