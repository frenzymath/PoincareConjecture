import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.Family








noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Side



theorem coordinate_bound_of_frontier_bound
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K)
    (f : X → Real) (hf : Continuous f) (hfo : IsOpenMap f) {c : Real}
    (hfront : ∀ x ∈ frontier K, f x ≤ c) : ∀ x ∈ K, f x ≤ c := by
  intro x hx
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩ hf.continuousOn
  have hpfront : p ∈ frontier K := by
    rw [hK.isClosed.frontier_eq]
    refine ⟨hp, ?_⟩
    intro hpi
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp
      (hfo (interior K) isOpen_interior) (f p) ⟨p, hpi, rfl⟩
    have hy : f p + r / 2 ∈ ball (f p) r := by
      rw [mem_ball, Real.dist_eq]
      simp only [add_sub_cancel_left, abs_of_pos (half_pos hr)]
      linarith
    obtain ⟨q, hq, he⟩ := hrsub hy
    have hle := hmax (interior_subset hq)
    change f q ≤ f p at hle
    rw [he] at hle
    linarith
  exact (hmax hx).trans (hfront p hpfront)


theorem coordinate_strict_bound_on_interior
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (f : X → Real) (hfo : IsOpenMap f) {c : Real}
    (hbound : ∀ x ∈ K, f x ≤ c) : ∀ x ∈ interior K, f x < c := by
  intro x hx
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp
    (hfo (interior K) isOpen_interior) (f x) ⟨x, hx, rfl⟩
  have hy : f x + r / 2 ∈ ball (f x) r := by
    rw [mem_ball, Real.dist_eq]
    simp only [add_sub_cancel_left, abs_of_pos (half_pos hr)]
    linarith
  obtain ⟨q, hq, he⟩ := hrsub hy
  have hle := hbound q (interior_subset hq)
  rw [he] at hle
  linarith



theorem intersection_eq_frontier_intersection_of_opposite_bounds
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (f : X → Real) (hf : Continuous f) (hfo : IsOpenMap f) {c : Real}
    (hleft : ∀ x ∈ frontier K, f x ≤ c)
    (hright : ∀ x ∈ frontier L, c ≤ f x) :
    K ∩ L = frontier K ∩ frontier L := by
  have hKbound := coordinate_bound_of_frontier_bound hK f hf hfo hleft
  have hneg : IsOpenMap (fun x => -f x) := (Homeomorph.neg Real).isOpenMap.comp hfo
  have hLbound : ∀ x ∈ L, -f x ≤ -c :=
    coordinate_bound_of_frontier_bound hL (fun x => -f x) hf.neg hneg
      (fun x hx => neg_le_neg (hright x hx))
  have hKstrict := coordinate_strict_bound_on_interior f hfo hKbound
  have hLstrict := coordinate_strict_bound_on_interior (fun x => -f x) hneg hLbound
  ext x
  constructor
  · rintro ⟨hxK, hxL⟩
    have he : f x = c := le_antisymm (hKbound x hxK) (neg_le_neg_iff.mp (hLbound x hxL))
    rw [hK.isClosed.frontier_eq, hL.isClosed.frontier_eq]
    exact ⟨⟨hxK, fun hx => (hKstrict x hx).ne he⟩,
      ⟨hxL, fun hx => (hLstrict x hx).ne (congrArg Neg.neg he)⟩⟩
  · rintro ⟨hxK, hxL⟩
    exact ⟨hK.isClosed.frontier_subset hxK, hL.isClosed.frontier_subset hxL⟩

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1



theorem filled_disk_coordinate_bound
    (B D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (i : Fin 2) {c : Real}
    (hboundary : ∀ p ∈ B '' sphere (0 : E2) 1, D p i ≤ c) :
    ∀ p ∈ B '' closedBall (0 : E2) 1, D p i ≤ c := by
  let L : E2 →L[Real] Real := EuclideanSpace.proj i
  have hLs : Function.Surjective L := by
    intro t
    exact ⟨PiLp.single 2 i t, by simp [L]⟩
  have hLo : IsOpenMap L := L.isOpenMap hLs
  apply coordinate_bound_of_frontier_bound
    ((isCompact_closedBall 0 1).image B.continuous) (fun p => D p i)
    (L.continuous.comp D.continuous) (hLo.comp D.toHomeomorph.isOpenMap)
  have he : B '' frontier (closedBall (0 : E2) 1) =
      frontier (B '' closedBall (0 : E2) 1) := B.toHomeomorph.image_frontier _
  rw [frontier_closedBall 0 one_ne_zero] at he
  intro p hp
  exact hboundary p (he.symm ▸ hp)



theorem filled_disks_inter_eq_boundary_inter_of_opposite_wall_sides
    (A B D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {c : Real}
    (hleft : ∀ p ∈ A '' sphere (0 : E2) 1, D p 0 ≤ c)
    (hright : ∀ p ∈ B '' sphere (0 : E2) 1, c ≤ D p 0) :
    (A '' closedBall (0 : E2) 1) ∩ (B '' closedBall (0 : E2) 1) =
      (A '' sphere (0 : E2) 1) ∩ (B '' sphere (0 : E2) 1) := by
  let L : E2 →L[Real] Real := EuclideanSpace.proj 0
  have hLs : Function.Surjective L := by
    intro t
    exact ⟨PiLp.single 2 0 t, by simp [L]⟩
  have hboundary (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
      frontier (F '' closedBall (0 : E2) 1) = F '' sphere (0 : E2) 1 := by
    have h : F '' frontier (closedBall (0 : E2) 1) =
        frontier (F '' closedBall (0 : E2) 1) := F.toHomeomorph.image_frontier _
    rw [frontier_closedBall 0 one_ne_zero] at h
    exact h.symm
  have he := intersection_eq_frontier_intersection_of_opposite_bounds
    ((isCompact_closedBall 0 1).image A.continuous)
    ((isCompact_closedBall 0 1).image B.continuous)
    (fun p => D p 0) (L.continuous.comp D.continuous)
    ((L.isOpenMap hLs).comp D.toHomeomorph.isOpenMap)
    (by simpa only [hboundary] using hleft)
    (by simpa only [hboundary] using hright)
  simpa only [hboundary] using he

namespace CircleFamily



theorem exists_disk_family_with_coordinate_bound
    {a b : Real} (A : CircleFamily a b)
    (D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (i : Fin 2) {c : Real}
    (hside : ∀ t ∈ Icc a b, ∀ p : S1, D (A.map (t, p)) i ≤ c) :
    ∃ C : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : Real × E2 => C z.1 z.2) ∧
      (∀ t ∈ Icc a b, C t '' sphere (0 : E2) 1 =
        range (fun p : S1 => A.map (t, p))) ∧
      (∀ t ∈ Icc a b, frontier (C t '' closedBall (0 : E2) 1) =
        range (fun p : S1 => A.map (t, p))) ∧
      ∀ t ∈ Icc a b, ∀ p ∈ C t '' closedBall (0 : E2) 1, D p i ≤ c := by
  obtain ⟨C, hC, hCs, hCf⟩ := A.exists_disk_family
  refine ⟨C, hC, hCs, hCf, ?_⟩
  intro t ht
  apply filled_disk_coordinate_bound (C t) D i
  intro p hp
  rw [hCs t ht] at hp
  obtain ⟨q, rfl⟩ := hp
  exact hside t ht q

end CircleFamily

end Poincare.Manifold.Schoenflies.Saddle.Wall.Side
