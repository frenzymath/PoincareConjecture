import PoincareConjecture.Proofs.M38.LinearCollarBall
import PoincareConjecture.Proofs.M38.SurgeryBallTopology

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_collared_region_complement
    {Q : GeneralizedSliceCarrier.{u}} {ι : Type*} {U : Set Q.carrier}
    (B : ι → SurgeryBallEmbedding Q)
    (hBsep : ∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall)
    (hUB : U = (⋃ i, (B i).closedBall)ᶜ)
    (c : ι → OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ∀ i, ContMDiffOn CylModel (𝓡 3) ∞ (c i) (c i).source)
    (hci : ∀ i, ContMDiffOn (𝓡 3) CylModel ∞ (c i).symm (c i).target)
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i)
    (hsource : ∀ i, univ ×ˢ Ioo (-δ i) (δ i) ⊆ (c i).source)
    (hzero : ∀ i, c i '' (univ ×ˢ ({0} : Set ℝ)) = frontier (B i).closedBall)
    (hpositive : ∀ i (z : UnitTwoSphere) (s : ℝ), 0 < s → s < δ i → c i (z, s) ∈ U) :
    ∃ D : ι → SurgeryBallEmbedding Q, ∃ r : ι → ℝ,
      (∀ i, 0 < r i ∧ r i < 1 / 2) ∧
      (∀ i, (D i).closedBall = (B i).closedBall) ∧
      (∀ i j, i ≠ j → Disjoint (D i).closedBall (D j).closedBall) ∧
      U = (⋃ i, (D i).closedBall)ᶜ ∧
      ∀ i (z : UnitTwoSphere) (s : ℝ), |s| < r i →
        (D i).map ((1 + s) • z.val) = c i (z, s) := by
  classical
  have hzero' (i) : c i '' (univ ×ˢ ({0} : Set ℝ)) =
      (surgeryBallPartialHomeomorph (B i)) '' Metric.sphere 0 1 := by
    change c i '' (univ ×ˢ ({0} : Set ℝ)) = (B i).map '' Metric.sphere 0 1
    rw [← surgeryBall_closedBall_frontier, hzero]
  have hpositive' (i) (z : UnitTwoSphere) (s : ℝ) (hs : 0 < s) (hsδ : s < δ i) :
      c i (z, s) ∉ (surgeryBallPartialHomeomorph (B i)) '' Metric.closedBall 0 1 := by
    have h := hpositive i z s hs hsδ
    rw [hUB] at h
    exact fun hi => h (mem_iUnion.mpr ⟨i, hi⟩)
  choose r D hr hrhalf hDB _ hmatch using fun i =>
    exists_surgeryBall_matching_linear_collar (surgeryBallPartialHomeomorph (B i))
      (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
      (B i).map_smooth (B i).inverse_smooth (c i) (hc i) (hci i)
      (hδ i) (hsource i) (hzero' i) (hpositive' i)
  have hDB' (i) : (D i).closedBall = (B i).closedBall := hDB i
  refine ⟨D, r, fun i => ⟨hr i, hrhalf i⟩, hDB', ?_, ?_, hmatch⟩
  · intro i j hij
    rw [hDB', hDB']
    exact hBsep i j hij
  · simpa only [hDB'] using hUB

end PoincareConjecture.M38
