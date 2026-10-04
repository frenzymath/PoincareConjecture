import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderRecursiveRecenter
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Collars.AlexanderRecursiveCollarSlab
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.FinitePositiveHeightGap

/-!
# The retained branching geometry of complete section profiles

Positive section charges retain their actual marked polygon
families and arbitrarily small collars for both centered
height signs. This is separate from geometric admissibility
at zero-charge events. See Alexander 1924, pp. 6--8 and
M76 derivations 269 and 274.
-/

set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every positive-charge section retains its complete
family, actual marked point, exact count, nonisolation and
both centered collars. The family and mark precede all
width choices. No claim about zero-charge sections is made.
See Alexander pp. 6--8 and M76 derivation 274. -/
def HasBranchingCollars (W : AlexanderSectionProfile E) : Prop :=
  ∀ c : ℝ, W.charge c ≠ 0 →
    ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)) (q : E),
      0 < m ∧
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      W.carrier ∩ {x | W.height x = c} = ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}) ∧
      (¬ Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) ∧
      alexanderCurveCount (fun i => (P i).boundary ℝ) = W.charge c ∧
      q ∈ closure ((W.carrier ∩ {x | W.height x = c}) \ {q}) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ β : ℝ, β ∈ Ioo 0 ε ∧ ∃ γ : ℝ, γ ∈ Ioo 0 ε ∧
          Nonempty (AlexanderCollarSlab W.carrier
            (W.height - AffineMap.const ℝ E c) q β) ∧
          Nonempty (AlexanderCollarSlab W.carrier
            (-(W.height - AffineMap.const ℝ E c)) q γ)

/-- Exact recentering preserves the same branching families
and collar witnesses. The centered affine maps agree on all
ambient points, not only on the section. See Alexander p. 7
and M76 derivation 274. -/
theorem HasBranchingCollars.recenter {W : AlexanderSectionProfile E}
    (hW : W.HasBranchingCollars) (c : ℝ) : (W.recenter c).HasBranchingCollars := by
  intro d hd
  obtain ⟨m, n, P, q, hm, hP, hfull, hpair, hbranch, hcount, hacc, hcollars⟩ :=
    hW (d + c) hd
  have hsection : (W.recenter c).carrier ∩ {x | (W.recenter c).height x = d} =
      W.carrier ∩ {x | W.height x = d + c} := by
    ext x
    change (x ∈ W.carrier ∧ W.height x - c = d) ↔
      (x ∈ W.carrier ∧ W.height x = d + c)
    exact and_congr_right fun _ => sub_eq_iff_eq_add
  have hheight : (W.recenter c).height - AffineMap.const ℝ E d =
      W.height - AffineMap.const ℝ E (d + c) := by
    ext x
    change W.height x - c - d = W.height x - (d + c)
    ring
  refine ⟨m, n, P, q, hm, hP, hsection.trans hfull, hpair, hbranch,
    hcount, ?_, ?_⟩
  · rwa [hsection]
  · intro ε hε
    simpa only [recenter_carrier, hheight] using hcollars ε hε

/-- Before choosing a supported deformation, one positive
width can avoid every nonzero event in any finite event set
and the actual charge support. The bound is arbitrary and
strict, including when that union has no nonzero element.
See Alexander pp. 6--8 and M76 derivation 274. -/
theorem exists_event_support_gap (W : AlexanderSectionProfile E)
    {C : Set ℝ} (hC : C.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, δ ∈ Ioo 0 ε ∧
      ∀ c ∈ C ∪ Function.support W.charge, c ≠ 0 → δ < |c| := by
  obtain ⟨δ, hδ, hgap⟩ := (hC.union W.finite_support).exists_pos_lt_positive_values
    (fun c : ℝ => |c|) hε
  exact ⟨δ, hδ, fun c hc hc0 => hgap c hc (abs_pos.mpr hc0)⟩

end Geometry.AlexanderSectionProfile
