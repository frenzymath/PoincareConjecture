import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.LocalDomains
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Interior
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem sourceSlab_agrees_of_map_eq
    (phi psi : C(H, H)) {A : Set X}
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior A → psi x = phi x)
    (u v : ℝ) : ∀ x ∈ Aᶜ, x ∈ sourceSlab psi u v ↔ x ∈ sourceSlab phi u v := by
  intro x hx
  by_cases hxR : x ∈ R
  · let xR : R := ⟨x, hxR⟩
    have hf := hfixed (latticeHandleDomainEquiv (Fin 1) (Fin 2) L xR)
      (by simpa only [Homeomorph.symm_apply_apply] using
        (fun h => hx (interior_subset h) : x ∉ interior A))
    rw [mem_sourceSlab_iff psi u v xR, mem_sourceSlab_iff phi u v xR]
    change (hamiltonOneHierarchyCoordinates (psi _)).2 ∈ _ ↔
      (hamiltonOneHierarchyCoordinates (phi _)).2 ∈ _
    rw [hf]
  · exact iff_of_false (fun h => hxR (sourceSlab_subset psi u v h))
      (fun h => hxR (sourceSlab_subset phi u v h))

theorem plDomain_complementary_sourceSlab_of_supported_map
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    (phi psi : C(H, H)) {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hold : PLDomain e (sourceSlab phi b (a + p)))
    (hnew : PLDomain e (sourceSlab psi a b))
    (hfront : frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
      (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)))
    {A : Set X} (hA : IsClosed A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior A → psi x = phi x) :
    PLDomain e (sourceSlab psi b (a + p)) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hclosed := (sourceSlab_isCompact psi b (a + p)).isClosed
  apply plDomain_of_two_open_agreements hnew.closed_exterior hold hclosed
    isOpen_interior hA.isOpen_compl
  · intro x _
    by_cases hx : x ∈ interior R
    · exact Or.inl hx
    · exact Or.inr (fun h => hx (hAR h))
  · exact complementary_sourceSlab_agrees_exterior psi ha hab hb hfront
  · exact sourceSlab_agrees_of_map_eq phi psi hfixed b (a + p)

end PoincareConjecture.M76.HamiltonIntervalTorus
