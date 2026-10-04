import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.CollarPatchGluing
import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Collars.CollarReparametrization

/-!
# Collaring a compact base from its actual local patches

Produce a finite compact refinement of the local patch sources,
merge the actual charts by finite induction, and reparametrize the
resulting open cylinder neighborhood. See Brown1962, Lemma1 and
Theorem1, pp333,337--338 and Brown derivation009.
-/

set_option autoImplicit false

open Set

namespace BrownCollar

variable {B X : Type*} [MetricSpace B] [CompactSpace B] [Nonempty B] [MetricSpace X]

/-- The compact case of Brown's local collar theorem, retaining an
actual homeomorphism and every original base value. Each supplied
local patch is an open partial homeomorphism of the literal cylinder;
the finite refinement and all overlap adjustments are constructed.
See Brown1962, Theorem1 and Brown derivations008--009. -/
theorem exists_full_collar_of_compact_local_patches
    (i : B → X) (hi : Function.Injective i)
    (hlocal : ∀ b : B,
      ∃ c : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) X,
        collarBase b ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = i a) :
    ∃ U : Set X, IsOpen U ∧ range i ⊆ U ∧
      ∃ c : (B × Ico (0 : ℝ) 1) ≃ₜ U, ∀ b, (c (collarBase b) : X) = i b := by
  classical
  choose c hpoint hbase using hlocal
  have hbcont : Continuous (collarBase : B → B × Ico (0 : ℝ) 1) :=
    continuous_id.prodMk continuous_const
  have hrefine (b : B) : ∃ K : Set B, IsCompact K ∧ b ∈ interior K ∧
      K ⊆ collarBase ⁻¹' (c b).source := by
    obtain ⟨K, hK, hbK, hKW⟩ := exists_compact_between
      (isCompact_singleton : IsCompact ({b} : Set B))
      ((c b).open_source.preimage hbcont) (singleton_subset_iff.mpr (hpoint b))
    exact ⟨K, hK, hbK (mem_singleton b), hKW⟩
  choose K hK hpointK hsourceK using hrefine
  obtain ⟨s, hcover⟩ := isCompact_univ.elim_finite_subcover
    (fun b => interior (K b)) (fun _ => isOpen_interior)
    (fun b _ => mem_iUnion.mpr ⟨b, hpointK b⟩)
  have hfinite (t : Finset B) :
      ∃ p : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) X,
        (∀ b ∈ ⋃ a ∈ t, K a, collarBase b ∈ p.source) ∧
          ∀ b, collarBase b ∈ p.source → p (collarBase b) = i b := by
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨c (Classical.arbitrary B), ?_, hbase (Classical.arbitrary B)⟩
      intro b hb
      simp at hb
    | @insert a t _hat ih =>
      obtain ⟨p, hpSource, hpBase⟩ := ih
      obtain ⟨q, hqSource, hqBase⟩ := exists_collar_patch_union p (c a) i hi
        (t.isCompact_biUnion (fun b _ => hK b)) (hK a) hpSource
        (fun b hb => hsourceK a hb) hpBase (hbase a)
      refine ⟨q, ?_, hqBase⟩
      intro b hb
      apply hqSource b
      obtain ⟨j, hj⟩ := mem_iUnion.mp hb
      obtain ⟨hjt, hbK⟩ := mem_iUnion.mp hj
      rcases Finset.mem_insert.mp hjt with hja | hjt
      · exact Or.inr (hja ▸ hbK)
      · exact Or.inl (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjt, hbK⟩⟩)
  obtain ⟨p, hpSource, hpBase⟩ := hfinite s
  have hsource (b : B) : collarBase b ∈ p.source := by
    apply hpSource b
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hcover (mem_univ b))
    obtain ⟨has, hbK⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨has, interior_subset hbK⟩⟩
  exact exists_full_collar_of_open_neighborhood p i hsource
    (fun b => hpBase b (hsource b))

end BrownCollar
