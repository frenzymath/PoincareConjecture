import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningNarrowedInsideGeometry

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.exists_half_height_of_spanning_side
    {X α F : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace F]
    {e : α → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e N j) {d U C : Set F} (hUd : U ⊆ d)
    (H : Disk ≃ₜ d)
    (hHrim : ∀ z : Disk,(z : V2) ∈ Rim ↔ (H z : F) ∈ U ∪ C)
    {k : F × ℝ → X}
    (hkP : ∀ z (hz : z ∈ d ×ˢ I),
      k z = P.map (H.symm ⟨z.1,hz.1⟩,z.2 / 2))
    {r : P2 → X}
    (hrSides : r '' (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ)) =
      k '' (U ×ˢ ({-1,1} : Set ℝ)))
    {x : X} (hx : x ∈ r '' (Icc (0 : ℝ) 1 ×ˢ ({-1,1} : Set ℝ))) :
    ∃ z : Disk,(z : V2) ∈ Rim ∧ (H z : F) ∈ U ∧
      ∃ positive : Bool,x = P.map (z,if positive then (1 : ℝ)/2 else -1/2) := by
  obtain ⟨⟨y,t⟩,⟨hy,ht⟩,hvalue⟩ := hrSides.subset hx
  let z : Disk := H.symm ⟨y,hUd hy⟩
  have hz : (H z : F) = y := congrArg Subtype.val (H.apply_symm_apply ⟨y,hUd hy⟩)
  have hzU : (H z : F) ∈ U := hz.symm ▸ hy
  refine ⟨z,(hHrim z).mpr (Or.inl hzU),hzU,?_⟩
  have htI : t ∈ I := by rcases ht with ht | ht <;> simp_all
  have heq : x = P.map (z,t/2) := hvalue.symm.trans (hkP (y,t) ⟨hUd hy,htI⟩)
  rcases ht with ht | ht
  · refine ⟨false,?_⟩
    have ht' : t = -1 := ht
    simpa only [ht',Bool.false_eq_true,reduceIte] using heq
  · refine ⟨true,?_⟩
    have ht' : t = 1 := ht
    simpa only [ht',reduceIte] using heq

end PoincareConjecture.M76
