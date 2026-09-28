import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Step

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

inductive SphereSurgeryTree (v : E3) (A : Finset Real) : (S2 -> E3) -> Type
  | leaf {f : S2 -> E3}
      (embedding : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
      (avoids : ∀ c ∈ A, ∀ p, inner Real v (f p) ≠ c) : SphereSurgeryTree v A f
  | branch {f : S2 -> E3} {c R : Real}
      (cut_mem : c ∈ A)
      (separated : ∀ k ∈ A, k ≠ c -> R < |k - c|)
      (step : SphereSurgeryStep f v c R)
      (minus : SphereSurgeryTree v A step.fMinus)
      (plus : SphereSurgeryTree v A step.fPlus) : SphereSurgeryTree v A f

namespace SphereSurgeryTree

variable {v : E3} {A : Finset Real} {f : S2 -> E3}

def leaves : {g : S2 -> E3} -> SphereSurgeryTree v A g -> List (S2 -> E3)
  | _, .leaf (f := g) _ _ => [g]
  | _, .branch _ _ _ minus plus => minus.leaves ++ plus.leaves

def Protects (B : Set Real) : {g : S2 -> E3} -> SphereSurgeryTree v A g -> Prop
  | _, .leaf _ _ => True
  | _, .branch (c := c) (R := R) _ _ _ minus plus =>
      (∀ k ∈ B, R < |k - c|) ∧ minus.Protects B ∧ plus.Protects B

theorem leaves_nonempty (tree : SphereSurgeryTree v A f) : tree.leaves ≠ [] := by
  induction tree with
  | leaf => simp [leaves]
  | branch _ _ _ _ _ ih _ =>
    intro h
    exact ih (List.append_eq_nil_iff.mp h).1

theorem embedding_of_mem_leaves (tree : SphereSurgeryTree v A f)
    {g : S2 -> E3} (hg : g ∈ tree.leaves) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g := by
  induction tree with
  | leaf hf _ =>
    simp only [leaves, List.mem_singleton] at hg
    subst g
    exact hf
  | branch _ _ _ _ _ ihM ihP =>
    rcases List.mem_append.mp hg with hm | hp
    · exact ihM hm
    · exact ihP hp

theorem avoids_of_mem_leaves (tree : SphereSurgeryTree v A f)
    {g : S2 -> E3} (hg : g ∈ tree.leaves) :
    ∀ c ∈ A, ∀ p, inner Real v (g p) ≠ c := by
  induction tree with
  | leaf _ hav =>
    simp only [leaves, List.mem_singleton] at hg
    subst g
    exact hav
  | branch _ _ _ _ _ ihM ihP =>
    rcases List.mem_append.mp hg with hm | hp
    · exact ihM hm
    · exact ihP hp

theorem induction_on_leaves (tree : SphereSurgeryTree v A f)
    (P : (S2 -> E3) -> Prop)
    (hleaf : ∀ g ∈ tree.leaves, P g)
    (hstep : ∀ {g c R}, c ∈ A ->
      (∀ k ∈ A, k ≠ c -> R < |k - c|) ->
      ∀ step : SphereSurgeryStep g v c R, P step.fMinus -> P step.fPlus -> P g) : P f := by
  induction tree with
  | leaf hf hav => exact hleaf _ (by simp [leaves])
  | branch hc hsep step minus plus ihM ihP =>
    apply hstep hc hsep step
    · exact ihM (fun g hg => hleaf g (List.mem_append_left _ hg))
    · exact ihP (fun g hg => hleaf g (List.mem_append_right _ hg))

end SphereSurgeryTree

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
