import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Bases
import PoincareConjecture.Proofs.M07.Topology.Gluing.Basic

open Set

universe u

namespace Poincare.Gluing

variable {S : Type u} [TopologicalSpace S]

universe v

variable {I : Type u} {P : I → Type v}
    [∀ i, TopologicalSpace (P i)]

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

theorem OverlapSystem.quotient_secondCountableTopology
    [Countable I] [∀ i, SecondCountableTopology (P i)]
    (D : OverlapSystem P) :
    SecondCountableTopology (Quotient D.setoid) :=
  TopologicalSpace.Quotient.secondCountableTopology D.quotient_mk_isOpenMap

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

theorem quotient_t2_of_isOpenMap_of_isClosed_components
    (r : Setoid (Sigma P))
    (hopen : IsOpenMap (Quotient.mk r : Sigma P → Quotient r))
    (hcomp : ∀ i j, IsClosed {q : P i × P j | r ⟨i, q.1⟩ ⟨j, q.2⟩}) :
    T2Space (Quotient r) :=
  quotient_t2_of_isOpenMap_of_isClosed_rel r hopen
    (isClosed_sigma_prod_relation r hcomp)

theorem OverlapSystem.quotient_t2Space
    (D : OverlapSystem P)
    (hclosed : ∀ i j, IsClosed {q : P i × P j |
      D.Rel ⟨i, q.1⟩ ⟨j, q.2⟩}) :
    T2Space (Quotient D.setoid) :=
  quotient_t2_of_isOpenMap_of_isClosed_components D.setoid
    D.quotient_mk_isOpenMap hclosed

end Poincare.Gluing
