import PoincareLib.Topology.Manifold.Surgery.Event.Ball.BallCoverDescent
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Descending a filled ball through a properly discontinuous cover

A compact neighborhood meets only finitely many of its translates. Separating
those translates gives an injective full ball chart downstairs, even when the
deck group is infinite. The construction retains the original closed ball,
center, and boundary image. Source: Morgan--Tian Proposition 15.3, pp. 357-358.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- A compact set disjoint from all its nonidentity translates has an open
neighborhood with the same property under a properly discontinuous action. -/
theorem exists_open_disjoint_translates_of_compact
    {X G : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [Group G] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X]
    {K : Set X} (hK : IsCompact K)
    (hdisjoint : ∀ g : G, g ≠ 1 → Disjoint K ((g • ·) '' K)) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∀ g : G, g ≠ 1 → Disjoint U ((g • ·) '' U) := by
  classical
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let S : Set G := {g | g ≠ 1 ∧ ((g • ·) '' L ∩ L).Nonempty}
  have hS : S.Finite :=
    (finite_disjoint_inter_image (Γ := G) hL hL).subset (fun _ hg => hg.2)
  let := hS.fintype
  obtain ⟨V, hV, hKV, hsep⟩ := exists_open_disjoint_finite_images_of_compact hK
    (fun g : S => (g.val • ·)) (fun g => continuous_const_smul g.val)
    (fun g => hdisjoint g.val g.property.1)
  refine ⟨V ∩ interior L, hV.inter isOpen_interior, fun _ hx => ⟨hKV hx, hKL hx⟩,
    fun g hg => ?_⟩
  by_cases hs : g ∈ S
  · exact (hsep ⟨g, hs⟩).mono inter_subset_left (image_mono inter_subset_left)
  · apply disjoint_left.mpr
    rintro z hz ⟨x, hx, hzx⟩
    exact hs ⟨hg, z, ⟨x, interior_subset hx.2, hzx⟩, interior_subset hz.2⟩

/-- Shortening the outer chart annulus makes the full ball chart disjoint
from every nonidentity deck translate while preserving its closed ball. -/
theorem exists_surgeryBall_with_disjoint_translates
    {A : GeneralizedSliceCarrier.{u}}
    {G : Type*} [Group G] [MulAction G A.carrier]
    [ContinuousConstSMul G A.carrier] [ProperlyDiscontinuousSMul G A.carrier]
    (B : SurgeryBallEmbedding A)
    (hdisjoint : ∀ g : G, g ≠ 1 → Disjoint B.closedBall ((g • ·) '' B.closedBall)) :
    ∃ D : SurgeryBallEmbedding A,
      D.closedBall = B.closedBall ∧ D.map 0 = B.map 0 ∧
        ∀ g : G, g ≠ 1 → Disjoint (D.map '' Metric.ball 0 2)
          ((g • ·) '' (D.map '' Metric.ball 0 2)) := by
  let : LocallyCompactSpace A.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) A.carrier
  obtain ⟨U, hU, hBU, hsep⟩ := exists_open_disjoint_translates_of_compact
    (surgeryBall_closedImage_compact B 1 (by norm_num)) hdisjoint
  obtain ⟨D, hD, hcenter, hDU⟩ := exists_surgeryBall_with_image_in_open B hU hBU
  exact ⟨D, hD, hcenter, fun g hg => (hsep g hg).mono hDU (image_mono hDU)⟩

/-- A ball separated from its deck translates descends through the supplied
smooth cover. Both the filled set and its exact frontier descend unchanged. -/
theorem exists_surgeryBall_descend_proper_fibers
    {A Q : GeneralizedSliceCarrier.{u}}
    {G : Type*} [Group G] [MulAction G A.carrier]
    [ContinuousConstSMul G A.carrier] [ProperlyDiscontinuousSMul G A.carrier]
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hfibers : ∀ x y, q x = q y → ∃ g : G, y = g • x)
    (B : SurgeryBallEmbedding A)
    (hdisjoint : ∀ g : G, g ≠ 1 → Disjoint B.closedBall ((g • ·) '' B.closedBall)) :
    ∃ D : SurgeryBallEmbedding Q,
      D.closedBall = q '' B.closedBall ∧ D.map 0 = q (B.map 0) ∧
        frontier D.closedBall = q '' frontier B.closedBall := by
  obtain ⟨C, hCB, hcenter, hsep⟩ :=
    exists_surgeryBall_with_disjoint_translates B hdisjoint
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞
      (q ∘ C.map) (Metric.ball 0 2) := by
    intro x
    exact (surgeryBall_map_localDiffeomorph A C x.property).comp (𝓡 3) Q.carrier
      (hq (C.map x.val))
  have hinj : Set.InjOn (q ∘ C.map) (Metric.ball 0 2) := by
    intro x hx y hy hxy
    obtain ⟨g, hg⟩ := hfibers (C.map x) (C.map y) hxy
    by_cases hunit : g = 1
    · subst g
      exact C.left_inverse.injOn hx hy (by simpa only [one_smul] using hg.symm)
    · exact (disjoint_left.mp (hsep g hunit) (mem_image_of_mem C.map hy)
        ⟨C.map x, mem_image_of_mem C.map hx, hg.symm⟩).elim
  let D := surgeryBallOfLocalDiffeomorph (q ∘ C.map) hlocal hinj
  refine ⟨D, ?_, ?_, ?_⟩
  · change (q ∘ C.map) '' Metric.closedBall 0 1 = q '' B.closedBall
    rw [image_comp]
    exact congrArg (fun S => q '' S) hCB
  · change q (C.map 0) = q (B.map 0)
    rw [hcenter]
  · rw [surgeryBall_closedBall_frontier D, ← hCB, surgeryBall_closedBall_frontier C]
    exact image_comp q C.map (Metric.sphere 0 1)

end PoincareMT.M38
