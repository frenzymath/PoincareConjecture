import Mathlib.Topology.Separation.Regular
import Mathlib.Data.Fintype.EquivFin










set_option autoImplicit false

open Set

namespace Geometry



theorem exists_finite_exception_neighborhoods
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {B : Set X} (hB : B.Finite) (W : B → Set X)
    (hW : ∀ x, IsOpen (W x)) (hxW : ∀ x, (x : X) ∈ W x) :
    ∃ (n : ℕ) (q : Fin n ≃ B) (V : Fin n → Set X),
      (∀ k, IsOpen (V k) ∧ (q k : X) ∈ V k ∧ IsCompact (closure (V k)) ∧
        closure (V k) ⊆ W (q k) ∧ B ∩ closure (V k) = {(q k : X)}) ∧
      Pairwise (fun k l ↦ Disjoint (closure (V k)) (closure (V l))) := by
  classical
  let _ : Fintype B := hB.fintype
  obtain ⟨U, hU, hdis⟩ := hB.t2_separation
  have hex (x : B) : ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
      closure V ⊆ U x ∩ W x ∧ IsCompact (closure V) := by
    obtain ⟨V, hV, hxV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := (x : X))) ((hU x).2.inter (hW x))
      (singleton_subset_iff.mpr ⟨(hU x).1, hxW x⟩)
    exact ⟨V, hV, singleton_subset_iff.mp hxV, hVU, hVc⟩
  choose V hVo hxV hVU hVc using hex
  let q := (Fintype.equivFin B).symm
  have hVD : Pairwise (fun x y : B ↦ Disjoint (closure (V x)) (closure (V y))) := by
    intro x y hxy
    exact (hdis x.property y.property (fun heq ↦ hxy (Subtype.ext heq))).mono
      (fun _ hx ↦ (hVU x hx).1) (fun _ hy ↦ (hVU y hy).1)
  refine ⟨Fintype.card B, q, V ∘ q, ?_, fun k l hkl ↦ hVD (q.injective.ne hkl)⟩
  intro k
  refine ⟨hVo _, hxV _, hVc _, fun x hx ↦ (hVU _ hx).2, ?_⟩
  ext x
  constructor
  · rintro ⟨hxB, hx⟩
    by_contra hne
    have hne' : (⟨x, hxB⟩ : B) ≠ q k := fun heq ↦ hne (congrArg Subtype.val heq)
    exact disjoint_left.mp (hVD hne') (subset_closure (hxV ⟨x, hxB⟩)) hx
  · rintro rfl
    exact ⟨(q k).property, subset_closure (hxV _)⟩



theorem pairwise_disjoint_exception_preimages
    {X Y α : Type*} [TopologicalSpace Y] (p : X → Y) (V : α → Set Y)
    (hdis : Pairwise (fun k l ↦ Disjoint (closure (V k)) (closure (V l)))) :
    Pairwise (fun k l ↦ Disjoint (p ⁻¹' closure (V k)) (p ⁻¹' closure (V l))) :=
  fun _ _ hne ↦ (hdis hne).preimage p

end Geometry
