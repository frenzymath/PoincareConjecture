import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CollarOverlapVanishing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalCutHomologyRetract
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CollarCoverHomotopyEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits HomologicalComplex

universe u v w
namespace PoincareConjecture.M76
open ModTwoMayerVietoris

theorem cut_inclusion_homology_injective
    {X : Type u} {κ : Type v} {ι : Type w}
    [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S : κ → Set X}
    (sS : ∀ i, ChartwisePLSphere e (S i))
    (R Q : Set X) (O : κ → Set X) (B : κ × Bool → Set X)
    (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (H : ∀ i b, S i ≃ₜ B (i, b))
    (hQ : Q = R \ ⋃ i, O i) (hcQ : IsClosed Q)
    (ho : ∀ i, IsOpen (O i))
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hinc : ∀ i, closure (O i) ∩ Q = B (i, false) ∪ B (i, true))
    (hW : ∀ i a, (W i (a, 0) : X) = H i false a ∧
      (W i (a, 1) : X) = H i true a) :
    Function.Injective (homologyMapOf
      (⟨Set.inclusion (hQ ▸ sdiff_subset), continuous_inclusion _⟩ : C(Q, R)) 1) := by
  have hcoords := marked_cut_collar_open_iff R Q O B W H hQ hCR hdis hinc hW
  let : CompactSpace (Metric.sphere (0 : Fin 3 → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : ∀ i, CompactSpace (S i) := fun i => (sS i).parametrization.compactSpace
  obtain ⟨hA, hB, hcover⟩ := collar_open_cover R O W ho hcoords
  have hz := CollarOverlap.marked_sphere_overlap_h1_isZero sS R Q O B W H
    hQ hCR hdis hinc hW
  have hsum := sum_injective_of_intersection_h1_zero
    (collarCoverOuter R W) (collarCoverInner R O) hA hB hcover hz
  let a : C(collarCoverOuter R W, R) := ⟨Subtype.val, continuous_subtype_val⟩
  have ha : Function.Injective (homologyMapOf a 1) := by
    have hm : Mono (sum (collarCoverOuter R W) (collarCoverInner R O) 1) :=
      (ModuleCat.mono_iff_injective _).mpr hsum
    have he : biprod.inl ≫ sum (collarCoverOuter R W) (collarCoverInner R O) 1 =
        homologyMapOf a 1 := biprod.inl_desc _ _
    have : Mono (homologyMapOf a 1) := he ▸ (inferInstance : Mono
      (biprod.inl ≫ sum (collarCoverOuter R W) (collarCoverInner R O) 1))
    exact (ModuleCat.mono_iff_injective _).mp this
  obtain ⟨E, hE⟩ := exists_collarCoverOuter_homotopyEquiv R Q O W
    hQ hcQ hCR hdis hcoords
  have he : Function.Injective (homologyMapOf E.invFun 1) :=
    CutGraph.moduleHomologyMap_section_injective coefficient E.toFun E.invFun E.right_inv 1
  have hmap : a.comp E.invFun =
      (⟨Set.inclusion (hQ ▸ sdiff_subset), continuous_inclusion _⟩ : C(Q, R)) := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hE x)
  have hcomp : homologyMapOf E.invFun 1 ≫ homologyMapOf a 1 =
      homologyMapOf (a.comp E.invFun) 1 := by
    unfold homologyMapOf chainMap
    rw [← homologyMap_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  rw [← hmap, ← hcomp]
  exact ha.comp he

end PoincareConjecture.M76
