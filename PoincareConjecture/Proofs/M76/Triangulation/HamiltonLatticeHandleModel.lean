import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Homeomorph.Lemmas












set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))



abbrev LatticeHandleAmbient := (ι → ℝ) × ((κ → ℝ) ⧸ L.toAddSubgroup)



def latticeHandleDomain : Set (LatticeHandleAmbient ι κ L) :=
  closedBall (0 : ι → ℝ) 1 ×ˢ univ



abbrev LatticeHandle :=
  closedBall (0 : ι → ℝ) 1 × ((κ → ℝ) ⧸ L.toAddSubgroup)



def latticeHandleBoundary : Set (LatticeHandle ι κ L) :=
  {a : closedBall (0 : ι → ℝ) 1 | ‖(a : ι → ℝ)‖ = 1} ×ˢ univ



def latticeHandleDomainEquiv :
    latticeHandleDomain ι κ L ≃ₜ LatticeHandle ι κ L :=
  (Homeomorph.Set.prod (closedBall (0 : ι → ℝ) 1)
    (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))).trans
    ((Homeomorph.refl (closedBall (0 : ι → ℝ) 1)).prodCongr
      (Homeomorph.Set.univ ((κ → ℝ) ⧸ L.toAddSubgroup)))



def latticeHandleMapInDomain
    (f : C(LatticeHandle ι κ L, LatticeHandle ι κ L)) :
    C(latticeHandleDomain ι κ L, latticeHandleDomain ι κ L) :=
  let q := latticeHandleDomainEquiv ι κ L
  (⟨q.symm, q.symm.continuous⟩ :
    C(LatticeHandle ι κ L, latticeHandleDomain ι κ L)).comp
      (f.comp ⟨q, q.continuous⟩)



def latticeHandleHomeomorphInDomain
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L) :
    latticeHandleDomain ι κ L ≃ₜ latticeHandleDomain ι κ L :=
  ((latticeHandleDomainEquiv ι κ L).trans g).trans
    (latticeHandleDomainEquiv ι κ L).symm






structure StandardLatticeHandleAtlas {α : Type*}
    (d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)) :
    Prop where
  domain : PLDomain d (latticeHandleDomain ι κ L)
  inverse_formula : ∀ j, ∃ a : (Fin 3 → ℝ) ≃ᴬ[ℝ] ((ι → ℝ) × (κ → ℝ)),
    ∀ z ∈ (d j).target,
      (d j).symm z = ((a z).1, QuotientAddGroup.mk (a z).2)

end PoincareConjecture.M76
