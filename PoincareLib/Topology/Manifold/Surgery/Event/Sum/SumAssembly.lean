import PoincareLib.Topology.Manifold.Surgery.Event.Sum.SumConnectedSum

/-!
# Adding one actual summand to a finite assembly

Lift all earlier connected-sum operations through the exact disjoint sum,
then append the supplied new operation. This preserves the original finite
piece family as the first block of the enlarged family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- A carrier forms the singleton disjoint union using its identity maps. -/
def singletonDisjointUnion (A : GeneralizedSliceCarrier.{u}) :
    SmoothDisjointUnionData (fun _ : Fin 1 => A) A where
  region := fun _ => Set.univ
  region_open := fun _ => isOpen_univ
  region_closed := fun _ => isClosed_univ
  identify := fun _ => {
    map := id
    inverse := id
    map_image := Set.image_id _
    inverse_image := Set.image_id _
    left_inverse := fun _ _ => rfl
    right_inverse := fun _ _ => rfl
    map_smooth := contMDiff_id.contMDiffOn
    inverse_smooth := contMDiff_id.contMDiffOn }
  pairwise_disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
  cover := Set.eq_univ_of_forall
    (fun x => Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩)

/-- A chain reaching a nonempty carrier starts at a nonempty carrier. -/
theorem connectedSumChain_source_nonempty {A C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) (hC : Nonempty C.carrier) :
    Nonempty A.carrier := by
  rcases h.cases_head with heq | ⟨B, hstep, _⟩
  · exact heq.symm ▸ hC
  · obtain ⟨D, E, ⟨U⟩, ⟨S⟩⟩ := hstep
    exact ⟨(U.identify 0).map (S.first_ball.map 0)⟩

/-- Keep all earlier operations and append a literal untouched singleton piece. -/
noncomputable def sumAssembly {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A : GeneralizedSliceCarrier.{u}} (S : SmoothFiniteConnectedSumAssembly pieces A)
    (D : GeneralizedSliceCarrier.{u}) (hA : Nonempty A.carrier) (hD : Nonempty D.carrier) :
    SmoothFiniteConnectedSumAssembly (Fin.append pieces (fun _ : Fin 1 => D))
      (sumCarrier A D) where
  initial := sumCarrier S.initial D
  disjoint_union := sumRefinement S.disjoint_union (singletonDisjointUnion D)
    (connectedSumChain_source_nonempty S.operations hA) hD
  operations := sumConnectedSumChain S.operations D

/-- A supplied connected-sum datum adds exactly its second carrier to the piece family. -/
noncomputable def appendConnectedSumAssembly {n : ℕ}
    {pieces : Fin n → GeneralizedSliceCarrier.{u}} {A B C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A) (K : SmoothConnectedSumData A B C) :
    SmoothFiniteConnectedSumAssembly (Fin.append pieces (fun _ : Fin 1 => B)) C :=
  (sumAssembly S B ⟨K.first_ball.map 0⟩ ⟨K.second_ball.map 0⟩).tail
    ⟨A, B, ⟨oneCapDisjointUnion A B ⟨K.first_ball.map 0⟩ ⟨K.second_ball.map 0⟩⟩, ⟨K⟩⟩

/-- Reassociation changes only finite indices, preserving all pieces and operations. -/
def reassociateAssembly {m n k : ℕ}
    {p : Fin m → GeneralizedSliceCarrier.{u}}
    {q : Fin n → GeneralizedSliceCarrier.{u}}
    {r : Fin k → GeneralizedSliceCarrier.{u}} {A : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly (Fin.append (Fin.append p q) r) A) :
    SmoothFiniteConnectedSumAssembly (Fin.append p (Fin.append q r)) A := by
  let e := finCongr (Nat.add_assoc m n k).symm
  have heq : (fun i => Fin.append (Fin.append p q) r (e i)) =
      Fin.append p (Fin.append q r) := by
    funext i
    rw [Fin.append_assoc]
    change Fin.append p (Fin.append q r) (Fin.cast (Nat.add_assoc m n k) (e i)) =
      Fin.append p (Fin.append q r) i
    rfl
  exact heq ▸ S.reindexM38 e

end PoincareMT.M38
