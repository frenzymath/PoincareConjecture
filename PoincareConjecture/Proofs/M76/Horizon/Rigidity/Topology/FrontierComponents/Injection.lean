import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.ComponentLoopReflection
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.PathMaps
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters

set_option autoImplicit false
open Set

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {S F T A B : Set X}

theorem inclusion_injective_of_whole_component (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S) (x : S) :
    Function.Injective (map (ContinuousMap.inclusion hSF) x) := by
  intro p q hpq
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      exact Path.Homotopic.Quotient.eq.mpr
        (Path.Homotopic.of_map_whole_component hSF hcomponent
          (Path.Homotopic.Quotient.eq.mp hpq))

theorem inclusion_injective_of_isClopen (hSF : S ⊆ F)
    (hS : IsClopen ((Subtype.val : F → X) ⁻¹' S)) (x : S) :
    Function.Injective (map (ContinuousMap.inclusion hSF) x) := by
  intro p q hpq
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    induction q using Path.Homotopic.Quotient.ind with
    | mk q =>
      obtain ⟨H⟩ := Path.Homotopic.Quotient.eq.mp hpq
      have hmem (z : unitInterval × unitInterval) : (H z : X) ∈ S := by
        apply hS.map_mem H.continuous (0, 0) _ z
        have h₀ : (H (0, 0) : X) = (x : X) :=
          congrArg Subtype.val ((H.map_zero_left 0).trans
            (p.map (continuous_inclusion hSF)).source)
        simpa only [mem_preimage, h₀] using x.property
      apply Path.Homotopic.Quotient.eq.mpr
      refine ⟨{
        toFun := fun z => ⟨H z, hmem z⟩
        continuous_toFun := (continuous_subtype_val.comp H.continuous).subtype_mk _
        map_zero_left := fun t => Subtype.ext
          (congrArg (fun y : F => (y : X)) (H.map_zero_left t))
        map_one_left := fun t => Subtype.ext
          (congrArg (fun y : F => (y : X)) (H.map_one_left t))
        prop' := fun t z hz => Subtype.ext
          (congrArg (fun y : F => (y : X)) (H.prop t z hz)) }⟩

theorem inclusion_injective_of_closed_partition
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hF : F = A ∪ B) (hAF : A ⊆ F) (x : A) :
    Function.Injective (map (ContinuousMap.inclusion hAF) x) := by
  have hcompl : ((Subtype.val : F → X) ⁻¹' A)ᶜ =
      (Subtype.val : F → X) ⁻¹' B := by
    ext y
    have hy : (y : X) ∈ A ∪ B := hF ▸ y.property
    exact ⟨fun h => hy.resolve_left h,
      fun hB hA => Set.disjoint_left.mp hAB hA hB⟩
  apply inclusion_injective_of_isClopen hAF _ x
  exact ⟨hA.preimage continuous_subtype_val,
    isClosed_compl_iff.mp (hcompl ▸ hB.preimage continuous_subtype_val)⟩

theorem inclusion_injective_comp (hSF : S ⊆ F) (hFT : F ⊆ T) (x : S)
    (h₁ : Function.Injective (map (ContinuousMap.inclusion hSF) x))
    (h₂ : Function.Injective (map (ContinuousMap.inclusion hFT)
      ((ContinuousMap.inclusion hSF) x))) :
    Function.Injective (map (ContinuousMap.inclusion (hSF.trans hFT)) x) := by
  have heq : ContinuousMap.inclusion (hSF.trans hFT) =
      (ContinuousMap.inclusion hFT).comp (ContinuousMap.inclusion hSF) := rfl
  rw [heq, map_comp]
  exact h₂.comp h₁

theorem whole_phase_component_ambient_injective
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hF : F = A ∪ B) (hSA : S ⊆ A)
    (hcomponent : ∀ x ∈ S, connectedComponentIn A x = S)
    (hinj : ∀ x : F, Function.Injective
      (map (⟨Subtype.val, continuous_subtype_val⟩ : C(F, X)) x)) (x : S) :
    Function.Injective (map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) x) := by
  have hAF : A ⊆ F := hF.symm ▸ subset_union_left
  have hSF := hSA.trans hAF
  have hcomponentInj := inclusion_injective_of_whole_component hSA hcomponent x
  have hphaseInj := inclusion_injective_of_closed_partition hA hB hAB hF hAF
    ((ContinuousMap.inclusion hSA) x)
  have hSFInj := inclusion_injective_comp hSA hAF x hcomponentInj hphaseInj
  have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(F, X)).comp
        (ContinuousMap.inclusion hSF) := rfl
  rw [heq, map_comp]
  exact (hinj ((ContinuousMap.inclusion hSF) x)).comp hSFInj

end FundamentalGroup
