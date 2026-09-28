import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Boundary.Labels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Contacts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.Normalization
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionStripBoundary

set_option autoImplicit false
open Set Geometry TriangleDiskModel PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "Model" => (TR ∪ TL : Set P2)

variable {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)

theorem copies_outer_iff
    (hcQ : ∀ j p, p ∈ source → (c j p ∈ frontier T ↔ p.1 = 0 ∨ p.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source)) :
    (∀ i (x : E.chain.retainedSet i),
      (E.chain.retainedCopy i x : P2) ∈ frontier Model ↔ (x : P2) ∈ frontier T) ∧
    (∀ b (x : source),
      (E.chain.stripCopy b x : P2) ∈ frontier Model ↔ (x : P2).1 = 0 ∨ (x : P2).1 = 1) := by
  classical
  let f : P2 → Bool := fun x ↦ decide (x ∈ frontier T)
  let u : P2 → Bool := fun x ↦ decide (x.1 = 0 ∨ x.1 = 1)
  have hf : f ⁻¹' {true} = frontier T := by ext x; simp [f]
  have hu : u ⁻¹' {true} = {x | x.1 = 0 ∨ x.1 = 1} := by ext x; simp [u]
  have hends : source ∩ u ⁻¹' {true} = stripEnds := by
    ext x
    simp only [hu, source, stripEnds, mem_inter_iff, mem_prod, mem_ofPred_eq,
      mem_insert_iff, mem_singleton_iff, mem_Icc]
    constructor
    · tauto
    · rintro ⟨h | h, hx⟩ <;> constructor
      · exact ⟨by rw [h]; norm_num, hx⟩
      · exact Or.inl h
      · exact ⟨by rw [h]; norm_num, hx⟩
      · exact Or.inr h
  have hmark (j b : Bool) :
      range (fun t : I01 ↦ c j ((t : ℝ), farArmParameter b)) ∩ f ⁻¹' {true} =
        {c j (0, farArmParameter b), c j (1, farArmParameter b)} := by
    rw [hf, ← arm_range]
    exact E.arm_outer j b
  have harm (a : ℝ) : arm a ∩ u ⁻¹' {true} = {(0, a), (1, a)} := by
    ext x
    simp only [hu, arm, mem_inter_iff, mem_prod, mem_singleton_iff, mem_ofPred_eq,
      mem_insert_iff, Prod.ext_iff]
    constructor
    · rintro ⟨⟨_, hx⟩, h | h⟩
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
    · rintro (⟨h, hx⟩ | ⟨h, hx⟩)
      · exact ⟨⟨by rw [h]; norm_num, hx⟩, Or.inl h⟩
      · exact ⟨⟨by rw [h]; norm_num, hx⟩, Or.inr h⟩
  have hlabel (j b : Bool) (t : I01) (a : ℝ) :
      f (c j ((t : ℝ), farArmParameter b)) = u ((t : ℝ), a) := by
    have hp : ((t : ℝ), farArmParameter b) ∈ source :=
      ⟨t.property, by cases b <;> norm_num [farArmParameter]⟩
    simp only [f, u, hcQ j _ hp]
  obtain ⟨g, hfront, hA, hL, hM, hR, hC⟩ := E.chain.exists_boundary_label f u {true}
    E.first_ball.isCompact.isClosed E.middle_ball.isCompact.isClosed E.last_ball.isCompact.isClosed
    (by rw [hf, E.first_ball.frontier_eq_of_finrank_eq rfl, arm_range])
    (by rw [hf, E.middle_ball.frontier_eq_of_finrank_eq rfl, arm_range, arm_range])
    (by rw [hf, E.last_ball.frontier_eq_of_finrank_eq rfl, arm_range])
    (by rw [hends]; exact stripRim_eq_ends_union_arms)
    (by simpa using hmark false (!E.s0)) (by simpa using hmark true E.s1)
    (by simpa using hmark false E.s0) (by simpa using hmark true (!E.s1))
    (harm 1) (harm (-1))
    (by rw [← arm_range, ← arm_range]
        exact hdis.symm.mono (image_mono (arm_far_subset_source _))
          (image_mono (arm_far_subset_source _)))
    (fun t ↦ hlabel false (!E.s0) t 1) (fun t ↦ hlabel true E.s1 t (-1))
    (fun t ↦ hlabel false E.s0 t (-1)) (fun t ↦ hlabel true (!E.s1) t 1)
  constructor
  · intro i x
    rw [hfront]
    have hv : g (E.chain.retainedCopy i x) = f x := by
      cases i
      · exact hA x
      · exact hM x
      · exact hC x
    simp only [mem_inter_iff, (E.chain.retainedCopy i x).property, true_and,
      mem_preimage, mem_singleton_iff, hv]
    simp [f]
  · intro b x
    rw [hfront]
    have hv : g (E.chain.stripCopy b x) = u x := by
      cases b
      · exact hL x
      · exact hR x
    simp only [mem_inter_iff, (E.chain.stripCopy b x).property, true_and,
      mem_preimage, mem_singleton_iff, hv]
    simp [u]

theorem normalized_copies_outer_iff (N : NonspanningChainAnnulus E.hole)
    (hcQ : ∀ j p, p ∈ source → (c j p ∈ frontier T ↔ p.1 = 0 ∨ p.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source)) :
    (∀ i (x : E.hole.sourceSet (.inl i)),
      depth 8 (N.copy (.inl i) x : P2) = -1 ↔ (x : P2) ∈ frontier T) ∧
    (∀ b (x : E.hole.sourceSet (.inr b)),
      depth 8 (N.copy (.inr b) x : P2) = -1 ↔ (x : P2).1 = 0 ∨ (x : P2).1 = 1) := by
  have h := E.copies_outer_iff hcQ hdis
  constructor
  · intro i x
    rw [N.outer, N.chart_copy]
    exact h.1 i ⟨x, x.property.1⟩
  · intro b x
    rw [N.outer, N.chart_copy]
    exact h.2 b x

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
