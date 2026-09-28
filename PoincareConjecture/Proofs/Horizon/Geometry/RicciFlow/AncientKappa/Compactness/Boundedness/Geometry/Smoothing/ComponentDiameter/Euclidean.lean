import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Components
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Bounded
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.AncientCompactness

abbrev CoordinateThree := EuclideanSpace ℝ (Fin 3)

private theorem bounded_side_subset_ball
    {S A B : Set CoordinateThree} {r : ℝ} (hr : 0 < r)
    (hSr : S ⊆ ball 0 r) (hA : IsOpen A) (hB : IsOpen B)
    (hdis : Disjoint A B) (hcover : A ∪ B = Sᶜ) (hbounded : Bornology.IsBounded A) :
    A ⊆ ball 0 r := by
  have hout : {x : CoordinateThree | r ≤ ‖x‖} ⊆ A ∪ B := by
    intro x hx
    rw [hcover]
    intro hxS
    have h := hSr hxS
    simp only [mem_ball, dist_zero_right] at h
    exact (not_le_of_gt h) hx
  have hpre := Poincare.Topology.isPreconnected_norm_ge
    (E := CoordinateThree) (by rw [← Module.finrank_eq_rank]; simp) hr
  rcases hpre.subset_or_subset hA hB hdis hout with hleft | hright
  · have hwhole : (univ : Set CoordinateThree) ⊆ ball 0 r ∪ A := by
      intro x _
      by_cases hx : ‖x‖ < r
      · exact Or.inl (by simpa only [mem_ball, dist_zero_right] using hx)
      · exact Or.inr (hleft (le_of_not_gt hx))
    exact False.elim (NormedSpace.unbounded_univ ℝ CoordinateThree
      ((isBounded_ball.union hbounded).subset hwhole))
  · intro x hx
    simp only [mem_ball, dist_zero_right]
    by_contra h
    exact Set.disjoint_left.mp hdis hx (hright (le_of_not_gt h))

theorem exists_critical_point_of_bounded_constant_boundary
    {A : Set CoordinateThree} (hA : IsOpen A) (hne : A.Nonempty)
    (hbounded : Bornology.IsBounded A) {f : CoordinateThree → ℝ}
    (hf : ContinuousOn f (closure A)) {c : ℝ}
    (hboundary : ∀ x ∈ frontier A, f x = c) :
    ∃ x ∈ A, fderiv ℝ f x = 0 := by
  have hcompact : IsCompact (closure A) := hbounded.isCompact_closure
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn hne.closure hf
  by_cases hxA : x ∈ A
  · exact ⟨x, hxA, (hmax.isLocalMax
      (Filter.mem_of_superset (hA.mem_nhds hxA) subset_closure)).fderiv_eq_zero⟩
  have hxfront : x ∈ frontier A := ⟨hx, by simpa only [hA.interior_eq] using hxA⟩
  have hxc := hboundary x hxfront
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hne.closure hf
  by_cases hyA : y ∈ A
  · exact ⟨y, hyA, (hmin.isLocalMin
      (Filter.mem_of_superset (hA.mem_nhds hyA) subset_closure)).fderiv_eq_zero⟩
  have hyfront : y ∈ frontier A := ⟨hy, by simpa only [hA.interior_eq] using hyA⟩
  have hyc := hboundary y hyfront
  obtain ⟨z, hz⟩ := hne
  have hzc : f z = c := le_antisymm (hxc ▸ hmax (subset_closure hz))
    (hyc ▸ hmin (subset_closure hz))
  have hzmax : IsMaxOn f (closure A) z := by
    intro w hw
    rw [hzc]
    exact hxc ▸ hmax hw
  exact ⟨z, hz, (hzmax.isLocalMax
    (Filter.mem_of_superset (hA.mem_nhds hz) subset_closure)).fderiv_eq_zero⟩

theorem exists_critical_point_in_ball_of_compact_connected_level_collar
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    {U : Set CoordinateThree} (hU : IsOpen U) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (e : (Y × Ioo (-s) s) ≃ₜ U)
    (himage : range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : CoordinateThree)) ⊆
      ball 0 r)
    {f : CoordinateThree → ℝ} (hf : ContinuousOn f (closedBall 0 r)) {c : ℝ}
    (hlevel : ∀ y : Y, f (e (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)) = c) :
    ∃ x ∈ ball (0 : CoordinateThree) r, fderiv ℝ f x = 0 := by
  let S := range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : CoordinateThree))
  obtain ⟨A, B, hA, hB, hAc, hBc, hdis, hcover, hAf, hBf, _, _⟩ :=
    Poincare.Topology.exists_collar_complementary_regions hs hU e
  have hS : IsCompact S := isCompact_range
    (continuous_subtype_val.comp (e.continuous.comp
      (continuous_id.prodMk continuous_const)))
  have hboundary (x : CoordinateThree) (hx : x ∈ S) : f x = c := by
    rcases hx with ⟨y, rfl⟩
    exact hlevel y
  rcases Poincare.Topology.bounded_side_of_compact_complement_partition_euclidean_three
    hS hA hB hdis hcover with ⟨hAb, _⟩ | ⟨hBb, _⟩
  · have hsub := bounded_side_subset_ball hr himage hA hB hdis hcover hAb
    have hclosure : closure A ⊆ closedBall (0 : CoordinateThree) r :=
      (closure_mono hsub).trans (closure_ball_subset_closedBall)
    obtain ⟨x, hx, hcrit⟩ := exists_critical_point_of_bounded_constant_boundary
      hA hAc.nonempty hAb (hf.mono hclosure)
        (fun x hx => hboundary x (by rw [hAf] at hx; exact hx))
    exact ⟨x, hsub hx, hcrit⟩
  · have hcover' : B ∪ A = Sᶜ := (union_comm B A).trans hcover
    have hsub := bounded_side_subset_ball hr himage hB hA hdis.symm hcover' hBb
    have hclosure : closure B ⊆ closedBall (0 : CoordinateThree) r :=
      (closure_mono hsub).trans (closure_ball_subset_closedBall)
    obtain ⟨x, hx, hcrit⟩ := exists_critical_point_of_bounded_constant_boundary
      hB hBc.nonempty hBb (hf.mono hclosure)
        (fun x hx => hboundary x (by rw [hBf] at hx; exact hx))
    exact ⟨x, hsub hx, hcrit⟩

end PoincareConjecture.AncientCompactness
