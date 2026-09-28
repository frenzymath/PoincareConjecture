import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.Region
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapSlice.Region

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.LowerAnnularEnd

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private instance : ConnectedSpace S1 := isConnected_iff_connectedSpace.mp
  (isConnected_sphere (by simp [← Module.finrank_eq_rank, E2]) (0 : E2) zero_le_one)

variable {v : E3} {g : S2 → E3} {B : Set Real}
  {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}

theorem mem_source_of_mem_height_interval (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) (q : S1) {t : Real} (ht : t ∈ Icc D.center b) :
    (q, t) ∈ A.chart.source := by
  rw [A.source]
  exact ⟨mem_univ _, by linarith [ht.1, A.delta_pos],
    by linarith [ht.2, A.delta_pos]⟩

theorem below_rim_subset_cap (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) (hDb : D.center < b) :
    A.chart '' (univ ×ˢ Ioo (a - A.delta) D.center) ⊆ D.chart '' ball 0 1 := by
  let V := A.chart '' (univ ×ˢ Ioo (a - A.delta) D.center)
  have hsub : univ ×ˢ Ioo (a - A.delta) D.center ⊆ A.chart.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    rw [A.source]
    exact ⟨mem_univ _, ht.1, by linarith [ht.2, A.delta_pos]⟩
  have hconn : IsPreconnected V :=
    (isPreconnected_univ.prod isPreconnected_Ioo).image A.chart
      (A.chart.continuousOn.mono hsub)
  have hfront : Disjoint V (frontier (D.chart '' ball (0 : E2) 1)) := by
    rw [ParallelDisks.frontier_image_ball zero_lt_one D.chart D.source D.smooth D.symm_smooth,
      ← A.boundary]
    apply disjoint_left.mpr
    rintro p ⟨⟨q, t⟩, hqt, rfl⟩ ⟨r, hr⟩
    have heq := congrArg Prod.snd (A.chart.injOn
      (A.mem_source_of_mem_height_interval haD r ⟨le_rfl, hDb.le⟩) (hsub hqt) hr)
    exact (ne_of_lt hqt.2.2) heq.symm
  obtain ⟨p, hp⟩ := D.isConnected_boundary.nonempty
  have hpcl : p ∈ closure (D.chart '' ball (0 : E2) 1) := by
    rw [ParallelDisks.closure_image_ball zero_lt_one D.chart D.source]
    exact image_mono sphere_subset_closedBall hp
  obtain ⟨q, hq⟩ := A.boundary.symm ▸ hp
  let O := A.chart '' (univ ×ˢ Ioo (a - A.delta) b)
  have hOs : univ ×ˢ Ioo (a - A.delta) b ⊆ A.chart.source := by
    rintro ⟨r, t⟩ ⟨_, ht⟩
    rw [A.source]
    exact ⟨mem_univ _, ht.1, by linarith [ht.2, A.delta_pos]⟩
  have hO : IsOpen O := A.chart.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) hOs
  have hpO : p ∈ O := by
    rw [← hq]
    exact mem_image_of_mem _ ⟨mem_univ _, by linarith [A.delta_pos], hDb⟩
  obtain ⟨z, hzO, hzD⟩ := mem_closure_iff.mp hpcl O hO hpO
  obtain ⟨⟨r, t⟩, hrt, rfl⟩ := hzO
  have ht : t < D.center := by
    by_contra hle
    have hge := le_of_not_gt hle
    have hh := A.height_le_center_of_mem_cap (image_mono ball_subset_closedBall hzD)
    rw [A.actual_height r t ⟨hge, hrt.2.2.le⟩] at hh
    have heq : t = D.center := le_antisymm hh hge
    have hzboundary : A.chart (r, t) ∈ frontier (D.chart '' ball (0 : E2) 1) := by
      rw [ParallelDisks.frontier_image_ball zero_lt_one D.chart D.source D.smooth
        D.symm_smooth, ← A.boundary, heq]
      exact mem_range_self r
    exact hzboundary.2 ((D.chart.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans D.source)).interior_eq.symm ▸ hzD)
  exact Poincare.Topology.subset_of_isPreconnected_of_disjoint_frontier
    (D.chart.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans D.source))
    hconn hfront ⟨_, mem_image_of_mem _ ⟨mem_univ _, hrt.2.1, ht⟩, hzD⟩

theorem chart_mem_interior_cappedRegion (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) {c : Real} (hDc : D.center < c) (hcb : c ≤ b)
    (q : S1) {t : Real} (ht : t ∈ Ico D.center c) :
    A.chart (q, t) ∈ _root_.interior (A.cappedRegion c) := by
  let O := A.chart '' (univ ×ˢ Ioo (a - A.delta) c)
  have hOs : univ ×ˢ Ioo (a - A.delta) c ⊆ A.chart.source := by
    rintro ⟨r, s⟩ ⟨_, hs⟩
    rw [A.source]
    exact ⟨mem_univ _, hs.1, by linarith [hs.2, A.delta_pos]⟩
  have hO : IsOpen O := A.chart.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) hOs
  apply interior_maximal (t := O) ?_ hO
  · exact mem_image_of_mem _ ⟨mem_univ _, by linarith [ht.1, A.delta_pos], ht.2⟩
  · rintro p ⟨⟨r, s⟩, ⟨_, hs⟩, rfl⟩
    by_cases hsd : s < D.center
    · exact Or.inl (image_mono ball_subset_closedBall
        (A.below_rim_subset_cap haD (hDc.trans_le hcb)
          (mem_image_of_mem _ ⟨mem_univ _, hs.1, hsd⟩)))
    · exact Or.inr (mem_image_of_mem _ ⟨mem_univ _, le_of_not_gt hsd, hs.2.le⟩)

theorem cap_subset_interior_cappedRegion (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) {c : Real} (hDc : D.center < c) (hcb : c ≤ b) :
    D.chart '' closedBall (0 : E2) 1 ⊆ _root_.interior (A.cappedRegion c) := by
  rintro p ⟨x, hx, rfl⟩
  rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hx) with hlt | heq
  · apply interior_maximal (t := D.chart '' ball (0 : E2) 1)
      (fun y hy => Or.inl (image_mono ball_subset_closedBall hy))
      (D.chart.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans D.source))
    exact mem_image_of_mem _ (mem_ball_zero_iff.mpr hlt)
  · have hb : D.chart x ∈ range (fun q : S1 => A.chart (q, D.center)) := by
      rw [A.boundary]
      exact mem_image_of_mem _ (mem_sphere_zero_iff_norm.mpr heq)
    obtain ⟨q, hq⟩ := hb
    rw [← hq]
    exact A.chart_mem_interior_cappedRegion haD hDc hcb q ⟨le_rfl, hDc⟩

theorem frontier_cappedRegion_subset_terminal (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) {c : Real} (hDc : D.center < c) (hcb : c ≤ b) :
    frontier (A.cappedRegion c) ⊆ range (fun q : S1 => A.chart (q, c)) := by
  intro p hp
  have hpK := (A.isCompact_cappedRegion haD hcb).isClosed.frontier_subset hp
  rcases hpK with hpD | ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  · exact (hp.2 (A.cap_subset_interior_cappedRegion haD hDc hcb hpD)).elim
  · rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact (hp.2 (A.chart_mem_interior_cappedRegion haD hDc hcb q ⟨ht.1, hlt⟩)).elim
    · exact mem_range_self q

theorem height_le_cut_of_mem_cappedRegion (A : LowerAnnularEnd D C h a b)
    {c : Real} (hDc : D.center ≤ c) (hcb : c ≤ b)
    {p : S2} (hp : p ∈ A.cappedRegion c) : inner Real v (g p) ≤ c := by
  rcases hp with hp | ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  · exact (A.height_le_center_of_mem_cap hp).trans hDc
  · rw [A.actual_height q t ⟨ht.1, ht.2.trans hcb⟩]
    exact ht.2

theorem slice_geometry (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) {c : Real} (hc : c ∈ Icc D.center b) :
    let f := fun q : S1 => A.chart (q, c)
    ContMDiff (𝓡 1) (𝓡 2) ∞ f ∧ Injective f ∧
      ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) f q) := by
  let f : S1 → S2 := fun q => A.chart (q, c)
  let j : S2 → S1 := fun p => (A.chart.symm p).1
  have hs (q : S1) := A.mem_source_of_mem_height_interval haD q hc
  have hf : ContMDiff (𝓡 1) (𝓡 2) ∞ f := fun q =>
    (A.smooth.contMDiffAt (A.chart.open_source.mem_nhds (hs q))).comp q
      ((contMDiff_id.prodMk contMDiff_const) q)
  have hjf : j ∘ f = id := by
    funext q
    exact congrArg Prod.fst (A.chart.left_inv (hs q))
  refine ⟨hf, (fun p q hpq => congrArg Prod.fst (A.chart.injOn (hs p) (hs q) hpq)), ?_⟩
  intro q
  have hj : MDifferentiableAt (𝓡 2) (𝓡 1) j (f q) :=
    (contMDiff_fst.contMDiffAt.comp (f q)
      (A.symm_smooth.contMDiffAt
        (A.chart.open_target.mem_nhds (A.chart.map_source (hs q))))).mdifferentiableAt (by simp)
  have hd := mfderiv_comp q hj (hf.mdifferentiable (by simp) q)
  rw [hjf, mfderiv_id] at hd
  intro x y hxy
  have hh := congrArg (mfderiv (𝓡 2) (𝓡 1) j (f q)) hxy
  exact (congrArg (fun L => L x) hd).trans (hh.trans (congrArg (fun L => L y) hd).symm)

theorem exists_cappedRegion_disk (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) {c : Real} (hDc : D.center < c) (hcb : c < b) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = A.cappedRegion c ∧
      d '' sphere (0 : E2) 1 = range (fun q : S1 => A.chart (q, c)) := by
  obtain ⟨hf, hi, hd⟩ := A.slice_geometry haD ⟨hDc.le, hcb.le⟩
  have hproper : A.cappedRegion c ≠ univ := by
    obtain ⟨q, hq⟩ := (NormedSpace.sphere_nonempty (E := E2)).mpr zero_le_one
    let t := (c + b) / 2
    intro heq
    have hh := A.height_le_cut_of_mem_cappedRegion hDc.le hcb.le
      (heq.symm ▸ mem_univ (A.chart (⟨q, hq⟩, t)))
    rw [A.actual_height _ t ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩] at hh
    dsimp [t] at hh
    linarith
  have hne : (_root_.interior (A.cappedRegion c) \
      range (fun q : S1 => A.chart (q, c))).Nonempty := by
    have hp : D.chart 0 ∈ D.chart '' closedBall (0 : E2) 1 :=
      mem_image_of_mem _ (mem_closedBall_self zero_le_one)
    refine ⟨D.chart 0, A.cap_subset_interior_cappedRegion haD hDc hcb.le hp, ?_⟩
    rintro ⟨q, hq⟩
    have hh := A.height_le_center_of_mem_cap hp
    rw [← hq, A.actual_height q c ⟨hDc.le, hcb.le⟩] at hh
    linarith
  exact exists_disk_neighborhood_of_frontier_subset_circle hf hi hd
    (A.isCompact_cappedRegion haD hcb.le).isClosed hproper
    (A.frontier_cappedRegion_subset_terminal haD hDc hcb.le) hne

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.LowerAnnularEnd
