import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimZeroHeight
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BoundaryDiskCollarCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_collar_pushed_boundary_disk
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (hcompat : ∀ i k, (e i).symm.trans (e k) ∈ piecewiseAffineGroupoid V3)
    (hj : PolyhedralPLInCharts e j D)
    (hjemb : Topology.IsEmbedding (fun x : D => j x))
    (hjB : MapsTo j D (frontier N))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier N) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hinside : MapsTo c (L.space ×ˢ I) N)
    (hbase : ∀ x : L.space, c ((x : E), 0) = HB x)
    (hproper : ∀ z : (L.space ×ˢ I : Set (E × ℝ)),
      c z ∈ frontier N ↔ (z : E × ℝ).2 = 0) :
    ∃ k : V2 → X, PolyhedralPLInCharts e k D ∧
      Topology.IsEmbedding (fun x : D => k x) ∧ MapsTo k D N ∧
      EqOn k j Q ∧ ∀ x : D, k x ∈ frontier N ↔ (x : V2) ∈ Q := by
  obtain ⟨q, hq, hqval⟩ := exists_finitePL_boundary_disk_collar_parameter
    hcompat hj hjB L hL HB c hc hi hbase
  obtain ⟨h, hh, hheight⟩ := exists_finitePL_square_rim_height
  have hqmap : MapsTo q D L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (HB.symm ⟨j x, hjB hx⟩).property
  have hrecover (x : D) : c (q x, 0) = j x := by
    rw [hqval x, hbase, HB.apply_symm_apply]
  let a : V2 → E × ℝ := fun x => (q x, h x)
  have hamap : MapsTo a D (L.space ×ˢ I) := by
    intro x hx
    exact ⟨hqmap hx, (hheight x hx).1.1,
      (hheight x hx).1.2.trans (by norm_num)⟩
  have haPL : FinitePiecewiseAffineOn a D := hq.prod_mk hh
  let k : V2 → X := c ∘ a
  have hkPL : PolyhedralPLInCharts e k D := by
    obtain ⟨T, hT, hTD, hTa⟩ := haPL
    have haT : FinitePiecewiseAffineOn a T.space := ⟨T, hT, rfl, hTa⟩
    have h := hc.comp_finitePiecewiseAffineOn T hT haT
      (fun _ hx => hamap (hTD.subset hx))
    exact hTD ▸ h
  have hkinj : InjOn k D := by
    intro x hx y hy hxy
    have hpair : (⟨a x, hamap hx⟩ : (L.space ×ˢ I : Set (E × ℝ))) =
        ⟨a y, hamap hy⟩ := hi.injective hxy
    have hqeq : q x = q y := congrArg
      (fun z : (L.space ×ˢ I : Set (E × ℝ)) => z.val.1) hpair
    have hjxy : j x = j y := by
      rw [← hrecover ⟨x, hx⟩, ← hrecover ⟨y, hy⟩, hqeq]
    have hsub : (⟨x, hx⟩ : D) = ⟨y, hy⟩ := hjemb.injective hjxy
    exact congrArg Subtype.val hsub
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V2) 1)
  have hkemb : Topology.IsEmbedding (fun x : D => k x) :=
    (hkPL.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hkinj x.property y.property hxy))).isEmbedding
  refine ⟨k, hkPL, hkemb, fun x hx => hinside (hamap hx), ?_, ?_⟩
  · intro x hx
    have hzero := (hheight x (sphere_subset_closedBall hx)).2.mpr hx
    change c (q x, h x) = j x
    rw [hzero]
    exact hrecover ⟨x, sphere_subset_closedBall hx⟩
  · intro x
    exact (hproper ⟨a x, hamap x.property⟩).trans (hheight x x.property).2

end PoincareConjecture.M76.Dehn
