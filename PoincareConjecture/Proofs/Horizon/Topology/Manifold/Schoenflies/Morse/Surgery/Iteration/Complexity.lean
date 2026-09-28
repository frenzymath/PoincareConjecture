import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Step.OtherLevels
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.Compact
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff BigOperators

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def sphereCutComplexity (v : E3) (A : Finset Real) (f : S2 -> E3) : Nat :=
  ∑ c ∈ A, Nat.card (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {c}))

theorem finite_height_level_components
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v : E3) (c : Real)
    (hc : ∀ p, inner Real v (f p) = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0) :
    Finite (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {c})) := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => inner Real v (f p)) :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  exact Poincare.Geometry.Manifold.RegularLevel.finite_connectedComponents_of_compact_regular_level
    (n := 1) hh c ((isClosed_singleton.preimage hh.continuous).isCompact) hc

theorem sphereCutComplexity_pos_of_nonempty_level
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v : E3) (A : Finset Real) {c : Real} (hcA : c ∈ A)
    (hc : ∀ p, inner Real v (f p) = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0)
    (hne : ((fun p => inner Real v (f p)) ⁻¹' {c}).Nonempty) :
    0 < sphereCutComplexity v A f := by
  let := finite_height_level_components hf v c hc
  let : Nonempty (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {c})) :=
    ⟨ConnectedComponents.mk ⟨hne.choose, hne.choose_spec⟩⟩
  have hpos : 0 < Nat.card
      (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {c})) := Finite.card_pos
  unfold sphereCutComplexity
  exact hpos.trans_le (Finset.single_le_sum
    (f := fun k => Nat.card (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {k})))
    (fun _ _ => Nat.zero_le _) hcA)

namespace SphereSurgeryStep

variable {f : S2 -> E3} {v : E3} {c R : Real}



theorem complexity_drop (S : SphereSurgeryStep f v c R) (A : Finset Real)
    (hcA : c ∈ A) (hsep : ∀ k ∈ A, k ≠ c -> R < |k - c|)
    (hregular : ∀ k ∈ A, ∀ p, inner Real v (f p) = k ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0) :
    sphereCutComplexity v A S.fMinus + sphereCutComplexity v A S.fPlus + 1 =
      sphereCutComplexity v A f := by
  classical
  let count := fun (g : S2 -> E3) (k : Real) =>
    Nat.card (ConnectedComponents ((fun p => inner Real v (g p)) ⁻¹' {k}))
  have hfinite (k : Real) (hk : k ∈ A) :
      Finite (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {k})) :=
    finite_height_level_components S.original_embedding v k (hregular k hk)
  let := hfinite c hcA
  have hcentral : count S.fMinus c + count S.fPlus c + 1 = count f c :=
    S.central_card_drop.2.2.1
  have hother (k : Real) (hk : k ∈ A.erase c) :
      count S.fMinus k + count S.fPlus k = count f k := by
    have hkA := Finset.mem_of_mem_erase hk
    let := hfinite k hkA
    exact (S.other_card (hsep k hkA (Finset.ne_of_mem_erase hk))).2.2
  have hrest : (∑ k ∈ A.erase c, count S.fMinus k) +
      (∑ k ∈ A.erase c, count S.fPlus k) = ∑ k ∈ A.erase c, count f k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hother
  have hsum (g : S2 -> E3) : sphereCutComplexity v A g =
      (∑ k ∈ A.erase c, count g k) + count g c :=
    (Finset.sum_erase_add A (count g) hcA).symm
  rw [hsum S.fMinus, hsum S.fPlus, hsum f]
  omega

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies
