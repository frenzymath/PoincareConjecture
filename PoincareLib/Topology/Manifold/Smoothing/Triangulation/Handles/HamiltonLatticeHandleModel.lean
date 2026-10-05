import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonPLDomainMaps
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The marked lattice model for Hamilton's handle torus

The lattice is the one used by the bounded-lift theorem. The subtype
of the boundaryless ambient product is identified with that theorem's
product by the canonical product-subtype homeomorphism. Standard
charts retain affine inverse formulas for the actual quotient map.
No atlas existence or rigidity theorem is asserted here. See Hamilton
1976, pp. 64--67 and M76 derivation 320.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

/-- The actual boundaryless ambient product of the marked lattice
handle. See Hamilton pp. 64--67 and M76 derivation 320. -/
abbrev LatticeHandleAmbient := (ι → ℝ) × ((κ → ℝ) ⧸ L.toAddSubgroup)

/-- The closed handle as a subset of its fixed boundaryless ambient.
See Hamilton pp. 64--67 and M76 derivation 320. -/
def latticeHandleDomain : Set (LatticeHandleAmbient ι κ L) :=
  closedBall (0 : ι → ℝ) 1 ×ˢ univ

/-- The exact product model consumed by `exists_boundedHandleLift`.
See Hamilton p. 67 and M76 derivations 89 and 320. -/
abbrev LatticeHandle :=
  closedBall (0 : ι → ℝ) 1 × ((κ → ℝ) ⧸ L.toAddSubgroup)

/-- The complete boundary marking used by the relative bounded lift.
See Hamilton p. 67 and M76 derivations 89 and 320. -/
def latticeHandleBoundary : Set (LatticeHandle ι κ L) :=
  {a : closedBall (0 : ι → ℝ) 1 | ‖(a : ι → ℝ)‖ = 1} ×ˢ univ

/-- The canonical product-subtype identification, without a new choice
of torus or boundary marking. See Hamilton p. 67 and derivation 320. -/
def latticeHandleDomainEquiv :
    latticeHandleDomain ι κ L ≃ₜ LatticeHandle ι κ L :=
  (Homeomorph.Set.prod (closedBall (0 : ι → ℝ) 1)
    (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))).trans
    ((Homeomorph.refl (closedBall (0 : ι → ℝ) 1)).prodCongr
      (Homeomorph.Set.univ ((κ → ℝ) ⧸ L.toAddSubgroup)))

/-- The same actual handle map viewed on the ambient domain subtype
by the fixed product-subtype identification. See derivation 320. -/
def latticeHandleMapInDomain
    (f : C(LatticeHandle ι κ L, LatticeHandle ι κ L)) :
    C(latticeHandleDomain ι κ L, latticeHandleDomain ι κ L) :=
  let q := latticeHandleDomainEquiv ι κ L
  (⟨q.symm, q.symm.continuous⟩ :
    C(LatticeHandle ι κ L, latticeHandleDomain ι κ L)).comp
      (f.comp ⟨q, q.continuous⟩)

/-- A homeomorphism viewed in the same fixed ambient-domain model.
See Hamilton p. 67 and M76 derivation 320. -/
def latticeHandleHomeomorphInDomain
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L) :
    latticeHandleDomain ι κ L ≃ₜ latticeHandleDomain ι κ L :=
  ((latticeHandleDomainEquiv ι κ L).trans g).trans
    (latticeHandleDomainEquiv ι κ L).symm

/-- Actual affine quotient-chart formulas for the standard structure
of the marked lattice handle. The complete original chart target is
retained, and its quotient map uses the given lattice L. This is a
certificate for a supplied atlas, not an atlas existence claim.
See Hamilton pp. 64--67 and M76 derivation 320. -/
structure StandardLatticeHandleAtlas {α : Type*}
    (d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)) :
    Prop where
  domain : PLDomain d (latticeHandleDomain ι κ L)
  inverse_formula : ∀ j, ∃ a : (Fin 3 → ℝ) ≃ᴬ[ℝ] ((ι → ℝ) × (κ → ℝ)),
    ∀ z ∈ (d j).target,
      (d j).symm z = ((a z).1, QuotientAddGroup.mk (a z).2)

end PoincareMT.M76
