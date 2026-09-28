import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskBaseFaces









set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}





theorem HamiltonProperDiskTriangulation.exists_interior_triangle_cofaces
    (T : HamiltonProperDiskTriangulation R D b)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hscard : s.card = 2)
    (hmeet : (convexHull ℝ (s : Set E) ∩ interior R).Nonempty) :
    ∃ t ∈ T.disk.faces, ∃ u ∈ T.disk.faces,
      s ⊆ t ∧ s ⊆ u ∧ t.card = 3 ∧ u.card = 3 ∧ t ≠ u ∧
      ∀ v ∈ T.disk.faces, s ⊆ v → v.card = 3 → v = t ∨ v = u := by
  classical
  obtain ⟨hi, hspace⟩ := T.original_parameter_image
  let L := T.inverse_affine.embeddedImage hi
  let q := s.image T.inverse
  have hL := T.inverse_affine.embeddedImage_finite hi (T.finite.subset T.disk_le)
  have hq : q ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  have hqc : q.card = Module.finrank ℝ V2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hscard] using
      Finset.card_image_iff.mpr (hi.mono (T.disk.subset_space hs))
  have hqmeet : (convexHull ℝ (q : Set V2) ∩ interior L.space).Nonempty := by
    obtain ⟨x, hxs, hxint⟩ := hmeet
    have hxD := T.disk_space.subset (T.disk.convexHull_subset_space hs hxs)
    let y := b.symm ⟨x, hxD⟩
    have hxy : T.inverse x = (y : V2) := T.inverse_eq ⟨x, hxD⟩
    refine ⟨T.inverse x, ?_, ?_⟩
    · rw [show (q : Set V2) = T.inverse '' (s : Set E) from Finset.coe_image,
        ← T.inverse_affine.image_convexHull hs]
      exact mem_image_of_mem T.inverse hxs
    · have hyle : ‖(y : V2)‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using y.property
      have hyne : ‖(y : V2)‖ ≠ 1 := by
        intro he
        have hyS : (y : V2) ∈ sphere 0 1 := by
          simpa only [mem_sphere, dist_zero_right] using he
        have hxf := (hproper y).mpr hyS
        change (b (b.symm ⟨x, hxD⟩) : E) ∈ frontier R at hxf
        have hxf' : x ∈ frontier R := by simpa only [b.apply_symm_apply] using hxf
        exact hxf'.2 hxint
      rw [hspace, interior_closedBall', hxy, mem_ball_zero_iff]
      exact lt_of_le_of_ne hyle hyne
  obtain ⟨y, hyq, hyint⟩ :=
    (convex_convexHull ℝ (q : Set V2)).intrinsicInterior_inter_open_nonempty
      isOpen_interior hqmeet
  obtain ⟨t, ht, u, hu, hqt, hqu, htc, huc, htu⟩ :=
    L.hasTwoFullCofaces_of_mem_interior hL hq hqc hyq hyint
  rw [T.inverse_affine.embeddedImage_faces] at ht hu
  obtain ⟨t₀, ht₀, rfl⟩ := ht
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  have hsubset {v w : Finset E} (hv : v ∈ T.disk.faces) (hw : w ∈ T.disk.faces)
      (hvw : v.image T.inverse ⊆ w.image T.inverse) : v ⊆ w := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp (hvw (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    exact hi (T.disk.subset_space hw hz) (T.disk.subset_space hv hx) hzx ▸ hz
  have hcard {v : Finset E} (hv : v ∈ T.disk.faces) :
      (v.image T.inverse).card = v.card := Finset.card_image_iff.mpr
        (hi.mono (T.disk.subset_space hv))
  have htc₀ : t₀.card = 3 := by simpa only [hcard ht₀,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using htc
  have huc₀ : u₀.card = 3 := by simpa only [hcard hu₀,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using huc
  refine ⟨t₀, ht₀, u₀, hu₀, hsubset hs ht₀ hqt, hsubset hs hu₀ hqu,
    htc₀, huc₀, fun he => htu (congrArg (fun v => v.image T.inverse) he), ?_⟩
  intro v hv hsv hvc
  have hvL : v.image T.inverse ∈ L.faces := by
    rw [T.inverse_affine.embeddedImage_faces]
    exact ⟨v, hv, rfl⟩
  have hvcL : (v.image T.inverse).card = Module.finrank ℝ V2 + 1 := by
    simp only [hcard hv, hvc, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rcases L.full_coface_eq_of_paired_facet hqc
    (by rw [T.inverse_affine.embeddedImage_faces]; exact ⟨t₀, ht₀, rfl⟩)
    (by rw [T.inverse_affine.embeddedImage_faces]; exact ⟨u₀, hu₀, rfl⟩)
    hvL htc huc hvcL hqt hqu (Finset.image_subset_image hsv) htu hyq with he | he
  · exact Or.inl (Finset.Subset.antisymm (hsubset hv ht₀ he.subset)
      (hsubset ht₀ hv he.symm.subset))
  · exact Or.inr (Finset.Subset.antisymm (hsubset hv hu₀ he.subset)
      (hsubset hu₀ hv he.symm.subset))

end PoincareConjecture.M76.HamiltonIndexOne
