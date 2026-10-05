import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Loop.SmoothEdge

/-!
# Relative coverage near a regular boundary join

Once the internal interfaces disappear from the local frontier, a regular
closed fitted union fills the actual Jordan side near the boundary point.
The smooth separator edge is constructed from the original return loop.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, including Claim 19.40,
pp. 470-471. These project constructions provide actual fitted boundary pieces and
contacts for the regional Gauss--Bonnet arguments.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- A fitted regular closed union whose local frontier lies on the actual return loop covers
the Jordan closure in a neighborhood of that point. Source:
`proof-work/tasks/M64/reports/2026-09-24-relative-boundary-cover.md`. -/
theorem m64Intrinsic_exists_relative_cover_of_local_frontier
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hp : p ∈ Ioo (0 : ℝ) T)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    {K : Set AnnulusCoordinates} (hK : IsClosed K)
    (hKregular : closure (interior K) = K) (hKsub : K ⊆ closure U)
    (hpK : gamma p ∈ K) {N : Set AnnulusCoordinates} (hN : N ∈ 𝓝 (gamma p))
    (hfrontK : N ∩ frontier K ⊆ gamma '' Icc 0 T) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧ W ∩ closure U ⊆ K := by
  obtain ⟨e, O, he, hinje, heloop, hO, hpO, hOloop⟩ :=
    m64Intrinsic_exists_loop_smooth_edge hg hend hinj hregular hp
  have hUregular := m64Intrinsic_jordan_interior_closure hU hV hdisj (hfU.trans hfV.symm)
  have hVregular := m64Intrinsic_jordan_interior_closure hV hU hdisj.symm (hfV.trans hfU.symm)
  have hthin : interior (e.map '' Icc (0 : ℝ) 1) = ∅ := by
    apply subset_empty_iff.mp
    rw [← interior_frontier (isClosed_closure : IsClosed (closure U))]
    apply interior_mono
    rwa [hUregular.2, hfU]
  have hdisjoint : Disjoint (interior K) (interior (closure V)) := by
    rw [hVregular.1]
    apply hdisj.mono_left
    rw [← hUregular.1]
    exact interior_mono hKsub
  have hpV : gamma p ∈ closure V := by
    apply frontier_subset_closure
    rw [hfV]
    exact ⟨p, ⟨hp.1.le, hp.2.le⟩, rfl⟩
  have hneighborhood : N ∩ O ∈ 𝓝 (e.map (1 / 2)) := by
    rw [he]
    exact inter_mem hN (hO.mem_nhds hpO)
  have hpinterior : gamma p ∈ interior (K ∪ closure V) := by
    rw [← he]
    apply e.mem_interior_union_of_local_frontiers (0 : AnnulusCoordinates)
      hinje (by intro z _; simp) hthin hK isClosed_closure hKregular
      (by rw [hVregular.1]) hdisjoint (by norm_num)
      (he ▸ hpK) (he ▸ hpV) hneighborhood
    · intro z hz
      exact hOloop ⟨hz.1.2, hfrontK ⟨hz.1.1, hz.2⟩⟩
    · intro z hz
      apply hOloop
      refine ⟨hz.1.2, ?_⟩
      simpa only [hVregular.2, hfV] using hz.2
  refine ⟨interior (K ∪ closure V), isOpen_interior, hpinterior, ?_⟩
  intro z hz
  apply hK.closure_subset
  apply mem_closure_iff.mpr
  intro O hO hzO
  obtain ⟨y, hy, hyU⟩ := mem_closure_iff.mp hz.2
    (O ∩ interior (K ∪ closure V)) (hO.inter isOpen_interior) ⟨hzO, hz.1⟩
  refine ⟨y, hy.1, ?_⟩
  rcases interior_subset hy.2 with hyK | hyV
  · exact hyK
  · exact False.elim (disjoint_left.mp (hdisj.closure_right hU) hyU hyV)

end PoincareMT
