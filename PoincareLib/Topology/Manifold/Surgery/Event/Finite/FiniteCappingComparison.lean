import PoincareLib.Topology.Manifold.Surgery.Event.Ball.BallRegionTransport
import PoincareLib.Topology.Manifold.Surgery.Event.Open.OpenRegionEquivalences

/-!
# Comparing finite cappings through their actual attaching annuli

An equivalence of the complements of finitely many closed balls extends
over the balls when its annular formula agrees with their original charts.
The resulting diffeomorphism keeps the complement map and every filled ball
pointwise. No equality or classification of the ambient carriers is assumed.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358, finite capping.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M38

variable {A D : GeneralizedSliceCarrier.{u}} {ι : Type v}
  (B : ι → SurgeryBallEmbedding A) (C : ι → SurgeryBallEmbedding D)
  (E : SurgeryRegionEquivalence A D (⋃ i, (B i).closedBall)ᶜ
    (⋃ i, (C i).closedBall)ᶜ)

/-- Extend the actual complement map across each of the displayed closed balls. -/
noncomputable def finiteBallComparisonMap (x : A.carrier) : D.carrier := by
  classical
  exact if h : ∃ i, x ∈ (B i).closedBall then
    (C (Classical.choose h)).map ((B (Classical.choose h)).inverse x)
  else E.map x

/-- Away from the closed filling balls the comparison is the given region map. -/
theorem finiteBallComparisonMap_complement {x : A.carrier}
    (hx : x ∈ (⋃ i, (B i).closedBall)ᶜ) :
    finiteBallComparisonMap B C E x = E.map x := by
  classical
  exact dif_neg (by simpa only [mem_compl_iff, mem_iUnion] using hx)

variable
  (hB : ∀ i j, i ≠ j →
    Disjoint ((B i).map '' Metric.ball 0 2) ((B j).map '' Metric.ball 0 2))
  (hC : ∀ i j, i ≠ j →
    Disjoint ((C i).map '' Metric.ball 0 2) ((C j).map '' Metric.ball 0 2))
  (hmatch : ∀ i (z : StandardCapSpace), z ∈ Metric.ball 0 2 → 1 < ‖z‖ →
    E.map ((B i).map z) = (C i).map z)

include hB in
/-- Inside a displayed radius-two chart, only that chart's own closed ball
can occur in the finite union. -/
theorem finiteCapping_mem_closedBall_iff {i : ι} {x : A.carrier}
    (hx : x ∈ (B i).map '' Metric.ball 0 2) :
    x ∈ ⋃ j, (B j).closedBall ↔ x ∈ (B i).closedBall := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    by_cases hji : j = i
    · simpa only [hji] using hj
    · exact (disjoint_left.mp (hB j i hji)
        (surgeryBall_closedBall_subset_image (B j) hj) hx).elim
  · exact fun h => mem_iUnion.mpr ⟨i, h⟩

variable [Finite ι]

omit [Finite ι] in
include hB hmatch in
/-- The extension is the literal filled-ball coordinate map throughout
the full radius-two chart, including the boundary and exterior annulus. -/
theorem finiteBallComparisonMap_chart (i : ι) {x : A.carrier}
    (hx : x ∈ (B i).map '' Metric.ball 0 2) :
    finiteBallComparisonMap B C E x = (C i).map ((B i).inverse x) := by
  classical
  by_cases h : ∃ j, x ∈ (B j).closedBall
  · have hi : Classical.choose h = i := by
      by_contra hne
      exact disjoint_left.mp (hB (Classical.choose h) i hne)
        (surgeryBall_closedBall_subset_image _ (Classical.choose_spec h)) hx
    simp only [finiteBallComparisonMap, dif_pos h, hi]
  · have hxout : x ∈ (⋃ j, (B j).closedBall)ᶜ := by
      simpa only [mem_compl_iff, mem_iUnion] using h
    rw [finiteBallComparisonMap_complement B C E hxout]
    have hxB : x ∉ (B i).closedBall := fun hxi => h ⟨i, hxi⟩
    have hnorm : 1 < ‖(B i).inverse x‖ :=
      lt_of_not_ge (fun hn => hxB ((surgeryBall_mem_closedBall_iff (B i) hx).mpr hn))
    simpa only [(B i).right_inverse hx] using
      hmatch i ((B i).inverse x) (surgeryBall_inverse_mem (B i) hx) hnorm

omit [Finite ι] in
include hB hmatch in
/-- In forward ball coordinates, the comparison preserves every parameter. -/
theorem finiteBallComparisonMap_ball (i : ι) (z : StandardCapSpace)
    (hz : z ∈ Metric.ball 0 2) :
    finiteBallComparisonMap B C E ((B i).map z) = (C i).map z := by
  rw [finiteBallComparisonMap_chart B C E hB hmatch i ⟨z, hz, rfl⟩,
    (B i).left_inverse hz]

include hB hmatch in
/-- The extended comparison is smooth on the whole actual source carrier. -/
theorem finiteBallComparisonMap_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finiteBallComparisonMap B C E) := by
  intro x
  by_cases hx : x ∈ ⋃ i, (B i).closedBall
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hxi := surgeryBall_closedBall_subset_image (B i) hi
    have hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞
        ((C i).map ∘ (B i).inverse) ((B i).map '' Metric.ball 0 2) :=
      (C i).map_smooth.comp (B i).inverse_smooth
        (fun _ hy => surgeryBall_inverse_mem (B i) hy)
    apply (hs.congr ?_).contMDiffAt ((surgeryBall_image_open (B i)).mem_nhds hxi)
    intro y hy
    exact finiteBallComparisonMap_chart B C E hB hmatch i hy
  · have hopen : IsOpen (⋃ i, (B i).closedBall)ᶜ :=
      (isClosed_iUnion_of_finite (fun i =>
        (surgeryBall_closedImage_compact (B i) 1 (by norm_num)).isClosed)).isOpen_compl
    apply (E.map_smooth.congr ?_).contMDiffAt (hopen.mem_nhds hx)
    intro y hy
    exact finiteBallComparisonMap_complement B C E hy

omit [Finite ι] in
include hB hmatch in
/-- The inverse complement map has the symmetric annular formula. -/
theorem finiteCapping_inverse_annulus (i : ι) (z : StandardCapSpace)
    (hz : z ∈ Metric.ball 0 2) (hn : 1 < ‖z‖) :
    E.inverse ((C i).map z) = (B i).map z := by
  have hmem : (B i).map z ∈ (⋃ j, (B j).closedBall)ᶜ := by
    intro h
    have hi := (finiteCapping_mem_closedBall_iff B hB ⟨z, hz, rfl⟩).mp h
    have hn' := (surgeryBall_mem_closedBall_iff (B i) ⟨z, hz, rfl⟩).mp hi
    rw [(B i).left_inverse hz] at hn'
    exact hn.not_ge hn'
  rw [← hmatch i z hz hn]
  exact E.left_inverse hmem

omit [Finite ι] in
include hB hC hmatch in
/-- The extended forward and inverse comparisons are inverse everywhere. -/
theorem finiteBallComparisonMap_left_inverse :
    Function.LeftInverse (finiteBallComparisonMap C B (reverseRegions E))
      (finiteBallComparisonMap B C E) := by
  intro x
  have hinverse := finiteCapping_inverse_annulus B C E hB hmatch
  by_cases hx : x ∈ ⋃ i, (B i).closedBall
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hxi := surgeryBall_closedBall_subset_image (B i) hi
    rw [finiteBallComparisonMap_chart B C E hB hmatch i hxi,
      finiteBallComparisonMap_ball C B (reverseRegions E) hC hinverse i
        ((B i).inverse x) (surgeryBall_inverse_mem (B i) hxi)]
    exact (B i).right_inverse hxi
  · have hy : E.map x ∈ (⋃ i, (C i).closedBall)ᶜ :=
      E.map_image.subset ⟨x, hx, rfl⟩
    rw [finiteBallComparisonMap_complement B C E hx,
      finiteBallComparisonMap_complement C B (reverseRegions E) hy]
    exact E.left_inverse hx

/-- Exact annular agreement extends the complement identification to a
genuine diffeomorphism between the two finite capped carriers. -/
noncomputable def finiteCappingDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) A.carrier D.carrier ∞ where
  toEquiv := {
    toFun := finiteBallComparisonMap B C E
    invFun := finiteBallComparisonMap C B (reverseRegions E)
    left_inv := finiteBallComparisonMap_left_inverse B C E hB hC hmatch
    right_inv := finiteBallComparisonMap_left_inverse C B (reverseRegions E) hC hB
      (finiteCapping_inverse_annulus B C E hB hmatch) }
  contMDiff_toFun := finiteBallComparisonMap_smooth B C E hB hmatch
  contMDiff_invFun := finiteBallComparisonMap_smooth C B (reverseRegions E) hC
    (finiteCapping_inverse_annulus B C E hB hmatch)

/-- The final diffeomorphism retains the original comparison on the exact complement. -/
theorem finiteCappingDiffeomorph_complement {x : A.carrier}
    (hx : x ∈ (⋃ i, (B i).closedBall)ᶜ) :
    finiteCappingDiffeomorph B C E hB hC hmatch x = E.map x :=
  finiteBallComparisonMap_complement B C E hx

/-- The final diffeomorphism retains the original chart on every inserted ball. -/
theorem finiteCappingDiffeomorph_ball (i : ι) (z : StandardCapSpace)
    (hz : z ∈ Metric.ball 0 2) :
    finiteCappingDiffeomorph B C E hB hC hmatch ((B i).map z) = (C i).map z :=
  finiteBallComparisonMap_ball B C E hB hmatch i z hz

end PoincareMT.M38
