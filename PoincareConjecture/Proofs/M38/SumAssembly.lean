import PoincareConjecture.Proofs.M38.SumConnectedSum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38


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


theorem connectedSumChain_source_nonempty {A C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) (hC : Nonempty C.carrier) :
    Nonempty A.carrier := by
  rcases h.cases_head with heq | ⟨B, hstep, _⟩
  · exact heq.symm ▸ hC
  · obtain ⟨D, E, ⟨U⟩, ⟨S⟩⟩ := hstep
    exact ⟨(U.identify 0).map (S.first_ball.map 0)⟩


noncomputable def sumAssembly {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {A : GeneralizedSliceCarrier.{u}} (S : SmoothFiniteConnectedSumAssembly pieces A)
    (D : GeneralizedSliceCarrier.{u}) (hA : Nonempty A.carrier) (hD : Nonempty D.carrier) :
    SmoothFiniteConnectedSumAssembly (Fin.append pieces (fun _ : Fin 1 => D))
      (sumCarrier A D) where
  initial := sumCarrier S.initial D
  disjoint_union := sumRefinement S.disjoint_union (singletonDisjointUnion D)
    (connectedSumChain_source_nonempty S.operations hA) hD
  operations := sumConnectedSumChain S.operations D


noncomputable def appendConnectedSumAssembly {n : ℕ}
    {pieces : Fin n → GeneralizedSliceCarrier.{u}} {A B C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces A) (K : SmoothConnectedSumData A B C) :
    SmoothFiniteConnectedSumAssembly (Fin.append pieces (fun _ : Fin 1 => B)) C :=
  (sumAssembly S B ⟨K.first_ball.map 0⟩ ⟨K.second_ball.map 0⟩).tail
    ⟨A, B, ⟨oneCapDisjointUnion A B ⟨K.first_ball.map 0⟩ ⟨K.second_ball.map 0⟩⟩, ⟨K⟩⟩


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

end PoincareConjecture.M38
