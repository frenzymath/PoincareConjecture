import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters



set_option autoImplicit false
open Set

namespace FundamentalGroup

variable {X : Type*} [TopologicalSpace X] {S F T A B : Set X}

theorem inclusion_injective_of_clopen_subset (hSF : S ⊆ F) (hFT : F ⊆ T)
    (hS : IsClopen ((Subtype.val : F → X) ⁻¹' S)) (x : F) (hx : (x : X) ∈ S)
    (hinj : Function.Injective (map (ContinuousMap.inclusion (hSF.trans hFT))
      (⟨x, hx⟩ : S))) :
    Function.Injective (map (ContinuousMap.inclusion hFT) x) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Path.Homotopic.Quotient.mk_surjective b
  have hmem (c : Path x x) (t : unitInterval) : (c t : X) ∈ S :=
    hS.map_mem c.continuous 0 (by simpa using hx) t
  let lift (c : Path x x) : Path (⟨x, hx⟩ : S) ⟨x, hx⟩ := {
    toFun := fun t => ⟨c t, hmem c t⟩
    continuous_toFun := (continuous_subtype_val.comp c.continuous).subtype_mk _
    source' := Subtype.ext (congrArg (fun y : F => (y : X)) c.source)
    target' := Subtype.ext (congrArg (fun y : F => (y : X)) c.target) }
  have h : Path.Homotopic.Quotient.mk (lift a) = Path.Homotopic.Quotient.mk (lift b) :=
    hinj hab
  exact congrArg (map (ContinuousMap.inclusion hSF) (⟨x, hx⟩ : S)) h

theorem inclusion_injective_of_disjoint_closed_union
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hF : F = A ∪ B) (hFT : F ⊆ T)
    (hinjA : ∀ (hAT : A ⊆ T) (x : A),
      Function.Injective (map (ContinuousMap.inclusion hAT) x))
    (hinjB : ∀ (hBT : B ⊆ T) (x : B),
      Function.Injective (map (ContinuousMap.inclusion hBT) x)) (x : F) :
    Function.Injective (map (ContinuousMap.inclusion hFT) x) := by
  have hAF : A ⊆ F := hF.symm ▸ subset_union_left
  have hBF : B ⊆ F := hF.symm ▸ subset_union_right
  have hcompl : ((Subtype.val : F → X) ⁻¹' A)ᶜ =
      (Subtype.val : F → X) ⁻¹' B := by
    ext y
    have hy : (y : X) ∈ A ∪ B := by rw [← hF]; exact y.property
    have hn := Set.disjoint_left.mp hAB
    simp only [mem_compl_iff, mem_preimage]
    exact ⟨fun h => hy.resolve_left h, fun hB hA => hn hA hB⟩
  have hclopen : IsClopen ((Subtype.val : F → X) ⁻¹' A) :=
    ⟨hA.preimage continuous_subtype_val,
      isClosed_compl_iff.mp (hcompl ▸ hB.preimage continuous_subtype_val)⟩
  have hx : (x : X) ∈ A ∪ B := by rw [← hF]; exact x.property
  rcases hx with hx | hx
  · exact inclusion_injective_of_clopen_subset hAF hFT hclopen x hx
      (hinjA (hAF.trans hFT) ⟨x, hx⟩)
  · have hclopenB : IsClopen ((Subtype.val : F → X) ⁻¹' B) := hcompl ▸ hclopen.compl
    exact inclusion_injective_of_clopen_subset hBF hFT hclopenB x hx
      (hinjB (hBF.trans hFT) ⟨x, hx⟩)

end FundamentalGroup
