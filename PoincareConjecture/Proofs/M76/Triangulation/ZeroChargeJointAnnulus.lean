import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem image_eq_of_boundary_fixed_finitePL_homotopy
    {N : Set E} (hN : IsCompact N) (hconn : IsConnected (interior N))
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (H : ℝ → E → E)
    (hpath : ∀ x ∈ N, ContinuousOn (fun t => H t x) (Icc 0 epsilon))
    (hPL : ∀ t ∈ Icc 0 epsilon, FinitePiecewiseAffineOn (H t) N)
    (hinj : ∀ t ∈ Icc 0 epsilon, InjOn (H t) N)
    (hfix : ∀ t ∈ Icc 0 epsilon, EqOn (H t) id (frontier N))
    (hzero : EqOn (H 0) id N) :
    ∀ t ∈ Icc 0 epsilon, H t '' N = N := by
  have hzeroI : (0 : ℝ) ∈ Icc 0 epsilon := ⟨le_rfl, hepsilon⟩
  have hinside (t : ℝ) (ht : t ∈ Icc 0 epsilon)
      (x : E) (hx : x ∈ interior N) : H t x ∈ interior N := by
    let P := (fun s => H s x) '' Icc 0 epsilon
    have hP : IsPreconnected P :=
      isPreconnected_Icc.image _ (hpath x (interior_subset hx))
    have havoid : Disjoint (frontier (interior N)) P := by
      apply disjoint_left.mpr
      rintro y hy ⟨s, hs, rfl⟩
      have hyfront : H s x ∈ frontier N := frontier_interior_subset hy
      have hyN : H s x ∈ N := hN.isClosed.frontier_subset hyfront
      have hsame : H s (H s x) = H s x := hfix s hs hyfront
      have hpoint : H s x = x := hinj s hs hyN (interior_subset hx) hsame
      exact hyfront.2 (hpoint.symm ▸ hx)
    have hstart : x ∈ P := ⟨0, hzeroI, hzero (interior_subset hx)⟩
    exact (hP.m76_subset_of_disjoint_frontier isOpen_interior havoid
      ⟨x, hstart, hx⟩) (mem_image_of_mem _ ht)
  intro t ht
  have himageClosed : IsClosed (H t '' N) :=
    (hN.image_of_continuousOn (hPL t ht).continuousOn).isClosed
  have hinsideImage (y : E) (hy : y ∈ H t '' N) (hyN : y ∈ interior N) :
      y ∈ interior (H t '' N) := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hxint : x ∈ interior N := by
      by_contra hxout
      have hxfront : x ∈ frontier N := ⟨subset_closure hx, hxout⟩
      have htx : H t x = x := hfix t ht hxfront
      exact hxout (htx ▸ hyN)
    exact (hPL t ht).mem_interior_image rfl (hinj t ht) hxint
  have hwholeInterior : interior N ⊆ interior (H t '' N) := by
    apply hconn.isPreconnected.subset_of_closure_inter_subset isOpen_interior
    · obtain ⟨x, hx⟩ := hconn.nonempty
      exact ⟨H t x, hinside t ht x hx,
        (hPL t ht).mem_interior_image rfl (hinj t ht) hx⟩
    · intro y hy
      have hyimage : y ∈ H t '' N :=
        (closure_minimal interior_subset himageClosed) hy.1
      exact hinsideImage y hyimage hy.2
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    by_cases hxint : x ∈ interior N
    · exact interior_subset (hinside t ht x hxint)
    · have htx : H t x = x := hfix t ht ⟨subset_closure hx, hxint⟩
      exact htx.symm ▸ hx
  · intro y hy
    by_cases hyint : y ∈ interior N
    · exact interior_subset (hwholeInterior hyint)
    · exact ⟨y, hy, hfix t ht ⟨subset_closure hy, hyint⟩⟩

omit [FiniteDimensional ℝ E] in

theorem exists_plane_homeomorph_of_annulus_image
    {N : Set E} {f : E → E} (hf : FinitePiecewiseAffineOn f N)
    (hinj : InjOn f N) (himage : f '' N = N)
    (hfix : EqOn f id (frontier N)) :
    ∃ G : E ≃ₜ E, EqOn G f N ∧ EqOn G id Nᶜ := by
  obtain ⟨e, _, he⟩ := hf.exists_homeomorph_image hinj
  let h : N ≃ₜ N := e.trans (Homeomorph.setCongr himage)
  have hh (x : N) : (h x : E) = f x := he x
  have hboundary (x : N) (hx : (x : E) ∈ frontier N) : h x = x :=
    Subtype.ext ((hh x).trans (hfix hx))
  let G := h.closedExtension hf.isCompact.isClosed hboundary
  refine ⟨G, ?_, ?_⟩
  · intro x hx
    exact (h.closedExtension_apply_mem hf.isCompact.isClosed hboundary hx).trans
      (hh ⟨x, hx⟩)
  · intro x hx
    exact h.closedExtension_apply_notMem hf.isCompact.isClosed hboundary hx

end PoincareConjecture.M76.ZeroChargeJoint
