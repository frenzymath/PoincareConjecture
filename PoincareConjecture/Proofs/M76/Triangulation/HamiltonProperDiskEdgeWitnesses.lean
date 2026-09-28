import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangleBoundary
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskDualIncidence
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualContact

set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

theorem HamiltonProperDiskTriangulation.exists_edge_chart_sign_witnesses
    (T : HamiltonProperDiskTriangulation R D b) (h3 : Module.finrank ℝ E = 3)
    (p : T.disk.vertices) {s t : Finset E} (hps : (p : E) ∈ s)
    (hs : s ∈ T.disk.faces) (hscard : s.card = 2)
    (ht : t ∈ T.ambient.faces) (htcard : t.card = 3) (hst : s ⊆ t)
    (hmeet : (convexHull ℝ (t : Set E) ∩ interior T.ambient.space).Nonempty)
    (A : V →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hzero : ∀ x ∈ t, A ((T.pairChart p).chart x) = 0) :
    let : Fintype T.ambient.faces := T.finite.fintype
    ∃ u ∈ T.ambient.faces, ∃ v ∈ T.ambient.faces,
      t ⊆ u ∧ t ⊆ v ∧ u.card = 4 ∧ v.card = 4 ∧
      u.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∧
      v.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∧
      A ((T.pairChart p).chart (u.centroid ℝ id)) < 0 ∧
      0 < A ((T.pairChart p).chart (v.centroid ℝ id)) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let H := (T.pairChart p).chart
  obtain ⟨x, hxt, hxint⟩ :=
    (convex_convexHull ℝ (t : Set E)).intrinsicInterior_inter_open_nonempty
      isOpen_interior hmeet
  obtain ⟨u, hu, v, hv, htu, htv, huc, hvc, huv⟩ :=
    T.ambient.hasTwoFullCofaces_of_mem_interior T.finite ht
      (htcard.trans h3.symm) hxt hxint
  have huc' : u.card = 4 := by simpa only [h3] using huc
  have hvc' : v.card = 4 := by simpa only [h3] using hvc
  have hstar {w : Finset E} (hw : w ∈ T.ambient.faces) (htw : t ⊆ w) :
      w ∈ (T.ambient.closedStar p).faces := by
    exact ⟨hw, by simpa only [Finset.insert_eq_of_mem (htw (hst hps))] using hw⟩
  have hsign := (T.star_affine p).opposite_centroid_signs
    (H.injOn.mono (T.star_source p)) (hstar ht Subset.rfl)
    (hstar hu htu) (hstar hv htv)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using htcard)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using huc')
    (by simpa only [Module.finrank_prod, Module.finrank_self] using hvc')
    htu htv huv A hA hzero
  have hmark {w : Finset E} (hw : w ∈ T.ambient.faces)
      (htw : t ⊆ w) (hwc : w.card = 4) :
      w.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space := by
    apply T.ambient.cofaceCentroid_mem_dualBlock_link (T.disk_le hs) hw (hst.trans htw)
    intro he
    rw [he] at hscard
    omega
  rcases hsign with h | h
  · exact ⟨u, hu, v, hv, htu, htv, huc', hvc', hmark hu htu huc',
      hmark hv htv hvc', h.1, h.2⟩
  · exact ⟨v, hv, u, hu, htv, htu, hvc', huc', hmark hv htv hvc',
      hmark hu htu huc', h.2, h.1⟩

theorem HamiltonProperDiskTriangulation.exists_edge_normal_witnesses
    (T : HamiltonProperDiskTriangulation R D b) (h3 : Module.finrank ℝ E = 3)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    (p : T.disk.vertices) {s t : Finset E} (hps : (p : E) ∈ s)
    (hs : s ∈ T.disk.faces) (hscard : s.card = 2)
    (ht : t ∈ T.disk.faces) (htcard : t.card = 3) (hst : s ⊆ t) :
    let : Fintype T.ambient.faces := T.finite.fintype
    ∃ u ∈ T.ambient.faces, ∃ v ∈ T.ambient.faces,
      t ⊆ u ∧ t ⊆ v ∧ u.card = 4 ∧ v.card = 4 ∧
      u.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∩ R ∧
      v.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∩ R ∧
      ((T.pairChart p).chart (u.centroid ℝ id)).2 < 0 ∧
      0 < ((T.pairChart p).chart (v.centroid ℝ id)).2 := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let H := (T.pairChart p).chart
  have hsubset : convexHull ℝ (t : Set E) ⊆ R :=
    (T.disk.convexHull_subset_space ht).trans (T.disk_space.subset.trans T.disk_subset_region)
  have hnonempty : (convexHull ℝ (t : Set E)).Nonempty :=
    (Finset.coe_nonempty.mpr (T.disk.nonempty_of_mem_faces ht)).convexHull
  obtain ⟨x, hxt⟩ := hnonempty
  have hzero : ∀ y ∈ t, (H y).2 = 0 := by
    intro y hy
    have htstar : t ∈ (T.ambient.closedStar p).faces :=
      ⟨T.disk_le ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using T.disk_le ht⟩
    have hyH := T.star_source p ((T.ambient.closedStar p).subset_space htstar hy)
    have hyD := T.disk_space.subset (T.disk.subset_space ht hy)
    rcases (T.pairChart p).model with ⟨_, hd⟩ | ⟨_, hd⟩
    · exact (hd y hyH).mp hyD
    · exact ((hd y hyH).mp hyD).2
  let A : V →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  have hA : A.linear ≠ 0 := by
    intro he
    have h := congrArg (fun m : V →ₗ[ℝ] ℝ => m ((0, 0), 1)) he
    change (1 : ℝ) = 0 at h
    exact one_ne_zero h
  obtain ⟨u, hu, v, hv, htu, htv, huc, hvc, hum, hvm, hun, hvp⟩ :=
    T.exists_edge_chart_sign_witnesses h3 p hps hs hscard (T.disk_le ht) htcard hst
      ⟨x, hxt, T.region_interior (hsubset hxt)⟩ A hA hzero
  have hinside := T.dualBlock_subset_interior ht (T.disk_triangle_not_boundary hproper ht htcard)
  have hmark {w : Finset E} (hw : w ∈ T.ambient.faces) (htw : t ⊆ w) :
      w.centroid ℝ id ∈ R := by
    apply interior_subset (hinside ?_)
    exact SimplicialComplex.space_subset_of_le (T.ambient.barycentricDualBlock_antitone htw)
      ((T.ambient.barycentricDualBlock w).vertices_subset_space
        (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices hw))
  exact ⟨u, hu, v, hv, htu, htv, huc, hvc, ⟨hum, hmark hu htu⟩,
    ⟨hvm, hmark hv htv⟩, hun, hvp⟩

end PoincareConjecture.M76.HamiltonIndexOne
