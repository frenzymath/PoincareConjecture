import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Bases
import PoincareLib.Topology.Gluing.Basic

/-!
Adapted from AxelWorkspace revision `f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e`,
`MorganTianLib/Ch05/FiniteGaussianQuotient/Separation.lean`.
See `references/analysis/axel-workspace/chart-gluing-reuse.md` for provenance.
-/


/-!
# Hausdorff separation for open quotient maps

An open quotient of a space by a closed equivalence relation is Hausdorff.
This is the separation criterion used by the finite Gaussian quotient
construction in Chapter 5.
-/

open Set

universe u

namespace Poincare.Gluing

variable {S : Type u} [TopologicalSpace S]

universe v

variable {I : Type u} {P : I → Type v}
    [∀ i, TopologicalSpace (P i)]

/-- The canonical quotient map of an overlap system is open because every open
set is the union of its open pieces and each piece map is open. -/
theorem OverlapSystem.quotient_mk_isOpenMap
    (D : OverlapSystem P) :
    IsOpenMap (Quotient.mk D.setoid : Sigma P → Quotient D.setoid) := by
  intro s hs
  have hdecomp : Set.image (Quotient.mk D.setoid) s =
      ⋃ i, D.include i '' (Sigma.mk i ⁻¹' s) := by
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases a with ⟨i, x⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨x, ha, rfl⟩⟩
    · intro hq
      rcases Set.mem_iUnion.mp hq with ⟨i, ⟨x, hx, hq⟩⟩
      exact ⟨⟨i, x⟩, hx, hq⟩
  rw [hdecomp]
  apply isOpen_iUnion
  intro i
  apply D.include_isOpenMap
  exact (isOpen_sigma_iff.mp hs i)

/-- A countable overlap quotient of second-countable pieces is second countable. -/
theorem OverlapSystem.quotient_secondCountableTopology
    [Countable I] [∀ i, SecondCountableTopology (P i)]
    (D : OverlapSystem P) :
    SecondCountableTopology (Quotient D.setoid) :=
  TopologicalSpace.Quotient.secondCountableTopology D.quotient_mk_isOpenMap

/- The product of two indexed disjoint unions, rearranged as an indexed union
of products. -/
private noncomputable def sigmaProdSigmaHomeomorph :
    (Sigma P × Sigma P) ≃ₜ Sigma (fun i => Sigma (fun j => P i × P j)) := by
  let fibre : ∀ i, P i × Sigma P ≃ₜ Sigma (fun j => P i × P j) := fun i =>
    let h₀ := (Homeomorph.prodComm (P i) (Sigma P)).trans
      (Homeomorph.sigmaProdDistrib (X := P) (Y := P i))
    let h₁ : Sigma (fun j => P j × P i) ≃ₜ Sigma (fun j => P i × P j) :=
      (IsHomeomorph.sigmaMap (f := id) Function.bijective_id
        (fun j => (Homeomorph.prodComm (P j) (P i)).isHomeomorph)).homeomorph _
    h₀.trans h₁
  let h₀ := Homeomorph.sigmaProdDistrib (X := P) (Y := Sigma P)
  let h₁ : Sigma (fun i => P i × Sigma P) ≃ₜ
      Sigma (fun i => Sigma (fun j => P i × P j)) :=
    (IsHomeomorph.sigmaMap (f := id) Function.bijective_id
      (fun i => (fibre i).isHomeomorph)).homeomorph _
  exact h₀.trans h₁

/- Closedness of a relation on a sigma-type can be checked on every pair of
fibres. -/
theorem isClosed_sigma_prod_relation
    (r : Setoid (Sigma P))
    (hcomp : ∀ i j, IsClosed {q : P i × P j | r ⟨i, q.1⟩ ⟨j, q.2⟩}) :
    IsClosed {p : (Sigma P) × (Sigma P) | r p.1 p.2} := by
  let R : Set (Sigma (fun i => Sigma (fun j => P i × P j))) :=
    {q | r ⟨q.1, q.2.2.1⟩ ⟨q.2.1, q.2.2.2⟩}
  have hR : IsClosed R := by
    rw [isClosed_sigma_iff]
    intro i
    rw [isClosed_sigma_iff]
    intro j
    simpa [R] using hcomp i j
  have heq : {p : (Sigma P) × (Sigma P) | r p.1 p.2} =
      sigmaProdSigmaHomeomorph ⁻¹' R := by
    ext p
    rcases p with ⟨⟨i, x⟩, ⟨j, y⟩⟩
    rfl
  rw [heq]
  exact sigmaProdSigmaHomeomorph.isClosed_preimage.mpr hR

/-- The quotient by a closed relation is Hausdorff when its canonical map is open.

The canonical quotient map is already a quotient map for the quotient topology;
openness therefore upgrades it to an open quotient map.  The kernel of this map
is exactly the given setoid relation, so the standard Hausdorff criterion for an
open quotient map applies.
-/
theorem quotient_t2_of_isOpenMap_of_isClosed_rel
    (r : Setoid S)
    (hopen : IsOpenMap (Quotient.mk r : S → Quotient r))
    (hclosed : IsClosed {p : S × S | r p.1 p.2}) :
    T2Space (Quotient r) := by
  apply (t2Space_iff_of_isOpenQuotientMap
    (IsOpenQuotientMap.of_isOpenMap_isQuotientMap hopen
      isQuotientMap_quotient_mk')).2
  have hrel : {q : S × S | Quotient.mk r q.1 = Quotient.mk r q.2} =
      {p : S × S | r p.1 p.2} := by
    ext p
    exact Quotient.eq
  rw [hrel]
  exact hclosed

/-- Hausdorffness of a sigma-type quotient from closed component kernels. -/
theorem quotient_t2_of_isOpenMap_of_isClosed_components
    (r : Setoid (Sigma P))
    (hopen : IsOpenMap (Quotient.mk r : Sigma P → Quotient r))
    (hcomp : ∀ i j, IsClosed {q : P i × P j | r ⟨i, q.1⟩ ⟨j, q.2⟩}) :
    T2Space (Quotient r) :=
  quotient_t2_of_isOpenMap_of_isClosed_rel r hopen
    (isClosed_sigma_prod_relation r hcomp)

/-- An overlap-system quotient is Hausdorff when every transition relation has
closed graph in its pair of component spaces. -/
theorem OverlapSystem.quotient_t2Space
    (D : OverlapSystem P)
    (hclosed : ∀ i j, IsClosed {q : P i × P j |
      D.Rel ⟨i, q.1⟩ ⟨j, q.2⟩}) :
    T2Space (Quotient D.setoid) :=
  quotient_t2_of_isOpenMap_of_isClosed_components D.setoid
    D.quotient_mk_isOpenMap hclosed


end Poincare.Gluing
