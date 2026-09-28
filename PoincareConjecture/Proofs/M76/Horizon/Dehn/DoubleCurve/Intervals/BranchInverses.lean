import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.MarkedModel
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeBranchInverse









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}


theorem OrdinaryIntervalMarkedModel.complete_core_preimage
    (D : OrdinaryIntervalMarkedModel old i) :
    D2 ∩ f ⁻¹' D.core = (D.clips 0).space ∪ (D.clips 1).space := by
  rw [(D.clips_data 0).2.1, (D.clips_data 1).2.1]
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    rcases D.full_preimage x hx (D.core_subset hfx) with h0 | h1
    · exact Or.inl ⟨h0, hfx⟩
    · exact Or.inr ⟨h1, hfx⟩
  · rintro (h0 | h1)
    · exact ⟨D.source_subset 0 h0.1, h0.2⟩
    · exact ⟨D.source_subset 1 h1.1, h1.2⟩



theorem OrdinaryIntervalMarkedModel.exists_branch_inverses
    (D : OrdinaryIntervalMarkedModel old i) :
    ∃ u : ∀ j : Fin 2, (D.marks (.inr j.castSucc)).space ≃ₜ (D.clips j.castSucc).space,
      (∀ j : Fin 2, (u j).IsFinitePL ∧ (u j).symm.IsFinitePL) ∧
      (∀ (j : Fin 2) (z : (D.marks (.inr j.castSucc)).space),
        f (u j z) = (D.inverse z : X)) ∧
      (∀ (j : Fin 2) (z : (D.marks (.inr j.castSucc)).space), D.graph (f (u j z)) = z) ∧
      (∀ (j : Fin 2) (x : (D.clips j.castSucc).space),
        ((u j).symm x : D.sample → ℝ × V3) = D.graph (f x)) ∧
      (∀ (j : Fin 2) (z : (D.marks (.inr j.castSucc)).space) (x : V2),
        x ∈ (D.source j.castSucc).space → f x = (D.inverse z : X) → x = (u j z : V2)) ∧
      D2 ∩ f ⁻¹' D.core = (D.clips 0).space ∪ (D.clips 1).space := by
  have hinj (j : Fin 2) : InjOn f (D.source j.castSucc).space := by
    have hem : IsEmbedding (fun x : (D.source j.castSucc).space ↦ f x) := by
      fin_cases j
      · exact D.left_embedding
      · exact D.right_embedding
    intro x hx y hy hxy
    exact congrArg Subtype.val (hem.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  obtain ⟨u, hPL, hvalue, hgraph, hinverse, hunique⟩ :=
    exists_original_signed_tube_branch_inverses D.core D.complex D.graph D.homeomorph
      D.inverse D.homeomorph_value D.inverse_value D.graph_separates
      (fun j : Fin 2 ↦ D.source j.castSucc) (fun j : Fin 2 ↦ D.clips j.castSucc)
      (fun j : Fin 2 ↦ D.marks (.inr j.castSucc)) (fun _ ↦ f) hinj
      (fun j ↦ (D.clips_data j.castSucc).2.1)
      (fun j ↦ (D.clips_data j.castSucc).2.2.1)
      (fun j ↦ (D.clips_data j.castSucc).2.2.2)
      (fun j ↦ (D.marks_full (.inr j.castSucc)).1)
  exact ⟨u, hPL, hvalue, hgraph, hinverse, hunique, D.complete_core_preimage⟩

end PoincareConjecture.M76.Dehn
