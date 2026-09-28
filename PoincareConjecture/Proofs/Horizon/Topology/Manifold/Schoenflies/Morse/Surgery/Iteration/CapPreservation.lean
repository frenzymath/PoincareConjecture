import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Tree
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Complexity
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Step.CapHeights
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.CutNeighborhoods



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryTree

variable {v : E3} {A : Finset Real}



def PreservesCaps : {f : S2 -> E3} -> SphereSurgeryTree v A f -> Prop
  | _, .leaf _ _ => True
  | _, .branch _ _ S minus plus =>
      minus.Protects S.capMinusHeights ∧ plus.Protects S.capPlusHeights ∧
        minus.PreservesCaps ∧ plus.PreservesCaps

theorem Protects.mono {B C : Set Real} {f : S2 -> E3}
    {tree : SphereSurgeryTree v A f} (h : tree.Protects B) (hCB : C ⊆ B) :
    tree.Protects C := by
  induction tree with
  | leaf => trivial
  | branch hc hsep S minus plus ihM ihP =>
    exact ⟨fun k hk => h.1 k (hCB hk), ihM h.2.1, ihP h.2.2⟩

end SphereSurgeryTree




theorem exists_sphereSurgeryTree_preserving_caps
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (A : Finset Real)
    (hregular : ∀ c ∈ A, ∀ p, inner Real v (f p) = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0)
    (B : Set Real) (hB : IsCompact B) (hdisj : Disjoint (A : Set Real) B) :
    ∃ tree : SphereSurgeryTree v A f, tree.Protects B ∧ tree.PreservesCaps := by
  classical
  have main : ∀ n : Nat, ∀ g : S2 -> E3,
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g ->
      (∀ c ∈ A, ∀ p, inner Real v (g p) = c ->
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) ->
      sphereCutComplexity v A g = n ->
      ∀ B : Set Real, IsCompact B -> Disjoint (A : Set Real) B ->
        ∃ tree : SphereSurgeryTree v A g, tree.Protects B ∧ tree.PreservesCaps := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hg hreg hn B hB hdisj
      by_cases hav : ∀ c ∈ A, ∀ p, inner Real v (g p) ≠ c
      · exact ⟨.leaf hg hav, trivial, trivial⟩
      push Not at hav
      obtain ⟨c, hc, p, hp⟩ := hav
      obtain ⟨R, hR, hsep, hprotected⟩ :=
        Poincare.Analysis.Calculus.Morse.exists_isolating_cut_radius_with_closed_heights
          A.finite_toSet hB.isClosed c (fun h => Set.disjoint_left.mp hdisj hc h)
      have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => inner Real v (g p)) :=
        (innerSL Real v).contMDiff.comp hg.contMDiff
      obtain ⟨S⟩ := nonempty_sphereSurgeryStep_of_smooth hg hh hv (fun _ => rfl)
        c (hreg c hc) ⟨p, hp⟩ hR
      obtain ⟨hregM, hregP⟩ := S.regular_on_cuts (A := (A : Set Real)) hsep hreg
      have hdrop := S.complexity_drop A hc hsep hreg
      have hM : sphereCutComplexity v A S.fMinus < n := by omega
      have hP : sphereCutComplexity v A S.fPlus < n := by omega
      obtain ⟨tM, htM, hcapM⟩ := ih _ hM S.fMinus S.fMinus_embedding hregM rfl
        (B ∪ S.capMinusHeights) (hB.union S.isCompact_capMinusHeights)
        (disjoint_union_right.mpr ⟨hdisj, S.disjoint_cuts_capMinusHeights hsep⟩)
      obtain ⟨tP, htP, hcapP⟩ := ih _ hP S.fPlus S.fPlus_embedding hregP rfl
        (B ∪ S.capPlusHeights) (hB.union S.isCompact_capPlusHeights)
        (disjoint_union_right.mpr ⟨hdisj, S.disjoint_cuts_capPlusHeights hsep⟩)
      refine ⟨.branch hc hsep S tM tP, ?_, ?_⟩
      · exact ⟨hprotected, htM.mono subset_union_left, htP.mono subset_union_left⟩
      · exact ⟨htM.mono subset_union_right, htP.mono subset_union_right, hcapM, hcapP⟩
  exact main _ f hf hregular rfl B hB hdisj

end Poincare.Manifold.Schoenflies
