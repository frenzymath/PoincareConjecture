import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Tree
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Cuts







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

namespace Poincare.Manifold.Schoenflies.SphereSurgeryTree

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private instance : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
  (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [E3]) (0 : E3) zero_le_one)

variable {v : E3} {A : Finset Real} {f : S2 → E3}



theorem height_range_subset_component (tree : SphereSurgeryTree v A f)
    {g : S2 → E3} (hg : g ∈ tree.leaves) (p : S2) :
    range (fun q => inner Real v (g q)) ⊆
      connectedComponentIn (A : Set Real)ᶜ (inner Real v (g p)) := by
  have hcontinuous : Continuous (fun q => inner Real v (g q)) :=
    (innerSL Real v).continuous.comp (tree.embedding_of_mem_leaves hg).contMDiff.continuous
  apply (isPreconnected_range hcontinuous).subset_connectedComponentIn (mem_range_self p)
  rintro y ⟨q, rfl⟩ hy
  exact tree.avoids_of_mem_leaves hg _ hy q rfl

private theorem critical_subsingleton_in_component
    {h : S2 → Real} {B : Set Real}
    (hseparation : ∀ p q, mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 →
      h q ∈ connectedComponentIn Bᶜ (h p) → p = q) (b : Real) :
    {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 ∧
      h p ∈ connectedComponentIn Bᶜ b}.Subsingleton := by
  intro p hp q hq
  apply hseparation p q hp.1 hq.1
  rw [← connectedComponentIn_eq hp.2]
  exact hq.2





theorem height_band_of_mem_leaves (tree : SphereSurgeryTree v A f)
    {g : S2 → E3} (hg : g ∈ tree.leaves) {h : S2 → Real}
    (hseparation : ∀ p q, mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 →
      h q ∈ connectedComponentIn (A : Set Real)ᶜ (h p) → p = q) :
    ∃ b ∈ (A : Set Real)ᶜ,
      range (fun q => inner Real v (g q)) ⊆ connectedComponentIn (A : Set Real)ᶜ b ∧
      IsConnected (connectedComponentIn (A : Set Real)ᶜ b) ∧
      {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 ∧
        h p ∈ connectedComponentIn (A : Set Real)ᶜ b}.Subsingleton := by
  let p : S2 := Classical.choice inferInstance
  have hp : inner Real v (g p) ∈ (A : Set Real)ᶜ := by
    intro hmem
    exact tree.avoids_of_mem_leaves hg _ hmem p rfl
  exact ⟨inner Real v (g p), hp, tree.height_range_subset_component hg p,
    isConnected_connectedComponentIn_iff.mpr hp,
    critical_subsingleton_in_component hseparation _⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryTree

end

end M38Schoenflies
