import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Constructions















open Set Topology

namespace Poincare.Gluing

universe u v

structure OverlapSystem {I : Type u} (P : I -> Type v)
    [forall i, TopologicalSpace (P i)] where
  transition : forall i j, OpenPartialHomeomorph (P i) (P j)
  self : forall i, transition i i = OpenPartialHomeomorph.refl (P i)
  inverse : forall i j, transition j i = (transition i j).symm
  comp_source : forall i j k x, x ∈ (transition i j).source ->
    transition i j x ∈ (transition j k).source -> x ∈ (transition i k).source
  comp_apply : forall i j k x, x ∈ (transition i j).source ->
    transition i j x ∈ (transition j k).source ->
    transition j k (transition i j x) = transition i k x

variable {I : Type u} {P : I -> Type v}
    [forall i, TopologicalSpace (P i)]

def OverlapSystem.Rel (D : OverlapSystem P) (a b : Sigma P) : Prop :=
  a.2 ∈ (D.transition a.1 b.1).source ∧ D.transition a.1 b.1 a.2 = b.2

theorem OverlapSystem.rel_equivalence (D : OverlapSystem P) :
    Equivalence D.Rel := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, x⟩
    simp [Rel, D.self]
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hx, hxy⟩
    dsimp only at hx hxy
    change y ∈ (D.transition j i).source ∧ D.transition j i y = x
    rw [D.inverse i j]
    constructor
    · simpa only [OpenPartialHomeomorph.symm_source, hxy] using
        (D.transition i j).map_source hx
    · exact (congrArg (D.transition i j).symm hxy.symm).trans
        ((D.transition i j).left_inv hx)
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨hx, hxy⟩ ⟨hy, hyz⟩
    dsimp only at hx hxy hy hyz
    change x ∈ (D.transition i k).source ∧ D.transition i k x = z
    have hy' : D.transition i j x ∈ (D.transition j k).source := by
      simpa only [hxy] using hy
    exact ⟨D.comp_source i j k x hx hy', (D.comp_apply i j k x hx hy').symm.trans
      ((congrArg (D.transition j k) hxy).trans hyz)⟩

def OverlapSystem.setoid (D : OverlapSystem P) : Setoid (Sigma P) where
  r := D.Rel
  iseqv := D.rel_equivalence

def OverlapSystem.include (D : OverlapSystem P) (i : I) (x : P i) :
    Quotient D.setoid := Quotient.mk D.setoid ⟨i, x⟩

theorem OverlapSystem.include_eq_iff (D : OverlapSystem P) (i j : I)
    (x : P i) (y : P j) :
    D.include i x = D.include j y ↔
      x ∈ (D.transition i j).source ∧ D.transition i j x = y :=
  Quotient.eq

theorem OverlapSystem.include_injective (D : OverlapSystem P) (i : I) :
    Function.Injective (D.include i) := by
  intro x y h
  have he := (D.include_eq_iff i i x y).mp h
  simpa [D.self] using he.2


theorem OverlapSystem.include_mem_range_iff (D : OverlapSystem P) (i j : I)
    (x : P i) :
    D.include i x ∈ Set.range (D.include j) ↔ x ∈ (D.transition i j).source := by
  constructor
  · rintro ⟨y, hy⟩
    exact ((D.include_eq_iff i j x y).mp hy.symm).1
  · intro hx
    exact ⟨D.transition i j x, ((D.include_eq_iff i j x _).mpr ⟨hx, rfl⟩).symm⟩

theorem OverlapSystem.include_preimage_image (D : OverlapSystem P)
    (i j : I) (s : Set (P i)) :
    D.include j ⁻¹' (D.include i '' s) =
      (D.transition j i).source ∩ D.transition j i ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have h := (D.include_eq_iff j i y x).mp hxy.symm
    exact ⟨h.1, by change D.transition j i y ∈ s; rw [h.2]; exact hx⟩
  · rintro ⟨hy, hs⟩
    exact ⟨D.transition j i y, hs, ((D.include_eq_iff j i y _).mpr ⟨hy, rfl⟩).symm⟩

theorem OverlapSystem.include_isOpenMap (D : OverlapSystem P) (i : I) :
    IsOpenMap (D.include i) := by
  intro s hs
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  rw [isOpen_sigma_iff]
  intro j
  change IsOpen (D.include j ⁻¹' (D.include i '' s))
  rw [D.include_preimage_image]
  exact (D.transition j i).isOpen_inter_preimage hs

theorem OverlapSystem.include_isOpenEmbedding (D : OverlapSystem P) (i : I) :
    IsOpenEmbedding (D.include i) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quotient_mk'.comp continuous_sigmaMk
  · exact D.include_injective i
  · exact D.include_isOpenMap i

theorem OverlapSystem.include_cover (D : OverlapSystem P) :
    (⋃ i, Set.range (D.include i)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact Set.mem_iUnion.mpr ⟨a.1, ⟨a.2, rfl⟩⟩

end Poincare.Gluing
