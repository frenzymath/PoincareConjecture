import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCapDisks
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.RegularLevelSeeds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_full_superlevel_disk_of_circle_level
    {h : S2 → Real} (hh : Continuous h) {b : Real}
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q))
    (hlevel : {q | h q = b} = range C)
    (hbelow : ∃ q, h q < b) {p : S2} (hp : b < h p) :
    ∃ m : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target ∧
      m '' closedBall 0 1 = {q | b ≤ h q} ∧
      m '' ball 0 1 = {q | b < h q} ∧
      m '' sphere (0 : E2) 1 = range C ∧
      m '' closedBall 0 1 = closure (connectedComponentIn (h ⁻¹' Ioi b) p) := by
  have hclosed : IsClosed {q : S2 | b ≤ h q} := isClosed_le continuous_const hh
  have hproper : {q : S2 | b ≤ h q} ≠ univ := by
    intro heq
    obtain ⟨q, hq⟩ := hbelow
    exact hq.not_ge (heq.symm.subset (mem_univ q))
  have hfront : frontier {q : S2 | b ≤ h q} ⊆ range C := by
    intro q hq
    have hf := hh.frontier_preimage_subset (Ici b) hq
    apply hlevel.subset
    simpa only [frontier_Ici, mem_preimage, mem_singleton_iff, mem_ofPred_eq] using hf
  have hopen : IsOpen {q : S2 | b < h q} := isOpen_lt continuous_const hh
  have hinside : {q : S2 | b < h q} ⊆ interior {q | b ≤ h q} :=
    hopen.subset_interior_iff.mpr (fun q hq => (show b < h q from hq).le)
  have hne : (interior {q : S2 | b ≤ h q} \ range C).Nonempty := by
    refine ⟨p, hinside hp, ?_⟩
    intro hpc
    have heq : h p = b := hlevel.symm.subset hpc
    exact hp.ne' heq
  obtain ⟨m, hs, hm, hmi, hc, hb⟩ :=
    exists_disk_neighborhood_of_frontier_subset_circle hC hCi hCd
      hclosed hproper hfront hne
  have hball : m '' ball (0 : E2) 1 = {q | b < h q} := by
    apply Subset.antisymm
    · rintro q ⟨x, hx, rfl⟩
      have hle : b ≤ h (m x) := hc.subset (mem_image_of_mem m (ball_subset_closedBall hx))
      apply lt_of_le_of_ne hle
      intro heq
      have hmc : m x ∈ range C := hlevel ▸ heq.symm
      obtain ⟨y, hy, hyx⟩ := hb.symm ▸ hmc
      have hxy := m.injOn (hs (sphere_subset_closedBall hy))
        (hs (ball_subset_closedBall hx)) hyx
      rw [hxy, mem_sphere_zero_iff_norm] at hy
      have hlt := mem_ball_zero_iff.mp hx
      linarith
    · rw [m.image_ball_eq_interior hs hc]
      exact hinside
  have hconn : IsPreconnected (h ⁻¹' Ioi b) := by
    rw [show h ⁻¹' Ioi b = m '' ball (0 : E2) 1 from hball.symm]
    exact isPreconnected_ball.image m
      (m.continuousOn.mono (ball_subset_closedBall.trans hs))
  have hcomp : connectedComponentIn (h ⁻¹' Ioi b) p = h ⁻¹' Ioi b :=
    (connectedComponentIn_subset _ _).antisymm
      (hconn.subset_connectedComponentIn hp Subset.rfl)
  refine ⟨m, hs, hm, hmi, hc, hball, hb, ?_⟩
  rw [hcomp]
  change m '' closedBall 0 1 = closure {q | b < h q}
  rw [← hball]
  exact (ParallelDisks.closure_image_ball zero_lt_one m hs).symm

theorem exists_full_superlevel_disk_of_regular_circle_level
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h) {b : Real}
    (hregular : ∀ q, h q = b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) C q))
    (hlevel : {q | h q = b} = range C) :
    ∃ p : S2, b < h p ∧ ∃ m : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target ∧
      m '' closedBall 0 1 = {q | b ≤ h q} ∧
      m '' ball 0 1 = {q | b < h q} ∧
      m '' sphere (0 : E2) 1 = range C ∧
      m '' closedBall 0 1 = closure (connectedComponentIn (h ⁻¹' Ioi b) p) := by
  let q : S1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hq : h (C q) = b := hlevel.symm.subset (mem_range_self q)
  obtain ⟨⟨x, _, hx⟩, ⟨p, _, hp⟩⟩ := exists_points_below_and_above_regular_level
    hh (hregular (C q) hq) hq isOpen_univ (mem_univ _)
  exact ⟨p, hp, exists_full_superlevel_disk_of_circle_level hh.continuous
    hC hCi hCd hlevel ⟨x, hx⟩ hp⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
