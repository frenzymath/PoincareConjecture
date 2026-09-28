import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkRetraction
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity
import PoincareConjecture.Proofs.M76.Mathlib.AffineSubspaceAvoidance











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]






theorem isConnected_faceLink_of_hull_meets_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hcodim : Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction + 1 <
      Module.finrank ℝ E)
    (hmeet : (convexHull ℝ (s : Set E) ∩ interior K.space).Nonempty) :
    IsConnected (K.faceLink s).space := by
  obtain ⟨x, hxs, hxint⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
      isOpen_interior hmeet
  let xK : K.space := ⟨x, interior_subset hxint⟩
  have hstar : (K.closedFaceStar s).space ∈ 𝓝[K.space] x := by
    rw [← map_nhds_subtype_val xK]
    exact K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hs xK hxs
  rw [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hxint)] at hstar
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hstar
  let A := affineSpan ℝ (s : Set E)
  let B := Metric.ball x ε \ (A : Set E)
  let D := (K.closedFaceStar s).space \ (A : Set E)
  have hBD : B ⊆ D := fun _ hy => ⟨hball hy.1, hy.2⟩
  have hconn : IsConnected B := by
    simpa only [B, iUnion_const] using
      (AffineSubspace.isPathConnected_sdiff_iUnion (fun _ : Unit => A)
        (fun _ => hcodim) Metric.isOpen_ball (convex_ball x ε)
        ⟨x, Metric.mem_ball_self hε⟩).isConnected
  obtain ⟨R, hRcont, hRmap, hRline⟩ := K.exists_continuous_faceLink_retraction hK s
  have himage : R '' B = (K.faceLink s).space := by
    apply subset_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hRmap (hBD hy)
    · intro y hy
      have hnear : ∀ᶠ r : ℝ in 𝓝[>] 0,
          AffineMap.lineMap x y r ∈ Metric.ball x ε :=
        AffineMap.lineMap_continuous.continuousWithinAt.eventually_mem
          (by simpa using Metric.ball_mem_nhds x hε)
      obtain ⟨r, hrball, hr⟩ := (hnear.and (Ioo_mem_nhdsGT zero_lt_one)).exists
      obtain ⟨hrD, hrR⟩ := hRline x (intrinsicInterior_subset hxs) y hy r
        ⟨hr.1, hr.2.le⟩
      exact ⟨AffineMap.lineMap x y r, ⟨hrball, hrD.2⟩, hrR⟩
  rw [← himage]
  exact hconn.image R (hRcont.mono hBD)

end Geometry.SimplicialComplex
