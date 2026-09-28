import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspacePunctureConnected
import PoincareConjecture.Proofs.M76.Mathlib.InteriorConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem isConnected_faceLink_of_halfspace_patch
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (ell : E →ᴬ[ℝ] ℝ) (hell : ell.toAffineMap.linear ≠ 0)
    (hhalf : K.space ⊆ {z | 0 ≤ ell z})
    (hzero : ∀ z ∈ affineSpan ℝ (s : Set E), ell z = 0)
    {V : Set E} (hV : IsOpen V)
    (hpatch : V ∩ {z | 0 ≤ ell z} ⊆ K.space)
    (hmeet : (convexHull ℝ (s : Set E) ∩ V).Nonempty) :
    IsConnected (K.faceLink s).space := by
  obtain ⟨x, hxs, hxV⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty hV hmeet
  let xK : K.space := ⟨x, K.convexHull_subset_space hs (intrinsicInterior_subset hxs)⟩
  have hstar : (K.closedFaceStar s).space ∈ 𝓝[K.space] x := by
    rw [← map_nhds_subtype_val xK]
    exact K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hs xK hxs
  obtain ⟨δ, hδ, hδstar⟩ := Metric.mem_nhdsWithin_iff.mp hstar
  have hsmall : V ∩ Metric.ball x δ ∈ 𝓝 x :=
    inter_mem (hV.mem_nhds hxV) (Metric.ball_mem_nhds x hδ)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  have hballstar : Metric.ball x ε ∩ {z | 0 ≤ ell z} ⊆ (K.closedFaceStar s).space := by
    intro z hz
    exact hδstar ⟨(hball hz.1).2, hpatch ⟨(hball hz.1).1, hz.2⟩⟩
  let A := affineSpan ℝ (s : Set E)
  let B := (Metric.ball x ε ∩ {z | 0 ≤ ell z}) \ (A : Set E)
  let D := (K.closedFaceStar s).space \ (A : Set E)
  have hBD : B ⊆ D := fun _ hy => ⟨hballstar hy.1, hy.2⟩
  have hconn : IsConnected B := by
    apply ell.isConnected_halfspace_sdiff hell Metric.isOpen_ball (convex_ball x ε)
    · refine ⟨x, Metric.mem_ball_self hε, ?_⟩
      change 0 ≤ ell x
      rw [hzero x (convexHull_subset_affineSpan _ (intrinsicInterior_subset hxs))]
    · intro z hz
      exact hzero z hz
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
      have hstarle : K.closedFaceStar s ≤ K := fun _ ht => ht.1
      have hrhalf : 0 ≤ ell (AffineMap.lineMap x y r) :=
        hhalf (space_subset_of_le hstarle hrD.1)
      exact ⟨AffineMap.lineMap x y r, ⟨⟨hrball, hrhalf⟩, hrD.2⟩, hrR⟩
  rw [← himage]
  exact hconn.image R (hRcont.mono hBD)

end Geometry.SimplicialComplex
