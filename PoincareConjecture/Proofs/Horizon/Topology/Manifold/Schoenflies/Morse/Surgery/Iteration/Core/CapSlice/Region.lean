import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.InwardDisk
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.ParallelDisks.Charts
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_disk_neighborhood_of_frontier_subset_circle
    {C : S1 → S2} (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (hCi : Injective C) (hCd : ∀ p, Injective (mfderiv (𝓡 1) (𝓡 2) C p))
    {K : Set S2} (hK : IsClosed K) (hproper : K ≠ univ)
    (hfront : frontier K ⊆ range C)
    (hne : (interior K \ range C).Nonempty) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = K ∧ d '' sphere (0 : E2) 1 = range C := by
  obtain ⟨e₀, e₁, hs₀, hs₁, he₀, hei₀, he₁, hei₁, hb₀, hb₁,
    _, hdis, hcover, _⟩ := exists_sphere_disk_neighborhoods_of_injective_mfderiv hC hCi hCd
  have hinside (e : OpenPartialHomeomorph E2 S2)
      (hb : e '' sphere (0 : E2) 1 = range C) :
      e '' closedBall 0 1 \ range C ⊆ e '' ball 0 1 := by
    rintro y ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨x, mem_ball_zero_iff.mpr ?_, rfl⟩
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx)
    intro heq
    exact hy (hb ▸ mem_image_of_mem e (mem_sphere_zero_iff_norm.mpr heq))
  have hdisfront (e : OpenPartialHomeomorph E2 S2)
      (hs : closedBall 0 1 ⊆ e.source)
      (hb : e '' sphere (0 : E2) 1 = range C) :
      Disjoint (e '' ball 0 1) (frontier K) := by
    apply disjoint_left.mpr
    intro p hp hpf
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, hyx⟩ := hb.symm ▸ hfront hpf
    have heq := e.injOn (hs (sphere_subset_closedBall hy)) (hs (ball_subset_closedBall hx)) hyx
    rw [heq, mem_sphere_zero_iff_norm] at hy
    have hlt := mem_ball_zero_iff.mp hx
    linarith
  have hconn (e : OpenPartialHomeomorph E2 S2) (hs : closedBall 0 1 ⊆ e.source) :
      IsPreconnected (e '' ball 0 1) :=
    (isPreconnected_ball : IsPreconnected (ball (0 : E2) 1)).image e
      (e.continuousOn.mono (ball_subset_closedBall.trans hs))
  have hidentify (d e : OpenPartialHomeomorph E2 S2)
      (hds : closedBall 0 1 ⊆ d.source) (hes : closedBall 0 1 ⊆ e.source)
      (hdb : d '' sphere (0 : E2) 1 = range C)
      (heb : e '' sphere (0 : E2) 1 = range C)
      (hcover : d '' closedBall 0 1 ∪ e '' closedBall 0 1 = univ)
      (hmeet : (d '' ball 0 1 ∩ interior K).Nonempty) : d '' closedBall 0 1 = K := by
    have hdin := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      (hconn d hds) (hdisfront d hds hdb) hmeet
    have hdc : d '' closedBall 0 1 ⊆ K := by
      rw [← ParallelDisks.closure_image_ball zero_lt_one d hds]
      exact closure_minimal (hdin.trans interior_subset) hK
    obtain ⟨q, hq⟩ := Set.nonempty_compl.mpr hproper
    have hqcover : q ∈ d '' closedBall 0 1 ∪ e '' closedBall 0 1 := hcover ▸ mem_univ q
    have hqe : q ∈ e '' ball 0 1 := by
      apply hinside e heb
      refine ⟨hqcover.resolve_left (fun h => hq (hdc h)), ?_⟩
      intro hqC
      exact hq (hdc (image_mono sphere_subset_closedBall (hdb.symm ▸ hqC)))
    have heout : e '' ball 0 1 ⊆ interior Kᶜ := by
      apply Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier (hconn e hes)
      · simpa only [frontier_compl] using hdisfront e hes heb
      · exact ⟨q, hqe, hK.isOpen_compl.interior_eq.symm ▸ hq⟩
    apply hdc.antisymm
    intro p hp
    by_contra hpd
    have hpe : p ∈ e '' ball 0 1 := by
      apply hinside e heb
      refine ⟨(hcover ▸ mem_univ p).resolve_left hpd, ?_⟩
      exact fun h => hpd (image_mono sphere_subset_closedBall (hdb.symm ▸ h))
    exact (interior_subset (heout hpe)) hp
  obtain ⟨p, hpi, hpC⟩ := hne
  have hpcover : p ∈ e₀ '' closedBall 0 1 ∪ e₁ '' closedBall 0 1 := hcover ▸ mem_univ p
  rcases hpcover with hp | hp
  · exact ⟨e₀, hs₀, he₀, hei₀,
      hidentify e₀ e₁ hs₀ hs₁ hb₀ hb₁ hcover ⟨p, hinside e₀ hb₀ ⟨hp, hpC⟩, hpi⟩, hb₀⟩
  · exact ⟨e₁, hs₁, he₁, hei₁,
      hidentify e₁ e₀ hs₁ hs₀ hb₁ hb₀ (by simpa only [union_comm] using hcover)
        ⟨p, hinside e₁ hb₁ ⟨hp, hpC⟩, hpi⟩, hb₁⟩

end Poincare.Manifold.Schoenflies
