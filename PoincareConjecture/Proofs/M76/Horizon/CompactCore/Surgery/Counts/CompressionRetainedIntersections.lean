import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
  {L U F : Set X} {j : (Fin 2 → ℝ) → X}

theorem retained_union_annulus (P : OriginalDiskProduct e L j) :
    (F \ P.openStrip) ∪ (F ∩ P.closedStrip) = F := by
  have hopen : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  ext x
  constructor
  · rintro (hx | hx) <;> exact hx.1
  · intro hx
    by_cases ho : x ∈ P.openStrip
    · exact Or.inr ⟨hx, hopen ho⟩
    · exact Or.inl ⟨hx, ho⟩

theorem retained_inter_annulus_eq_inter_endDisks (P : OriginalDiskProduct e L j) :
    (F \ P.openStrip) ∩ (F ∩ P.closedStrip) =
      (F \ P.openStrip) ∩ P.endDisks := by
  rw [← P.closedStrip_sdiff_openStrip]
  ext x
  simp only [mem_inter_iff, mem_sdiff]
  tauto

theorem retained_inter_capDisk (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (closedBall 0 1 ×ˢ Icc (-1 : ℝ) 1) U) (b : Bool) :
    (F \ P.openStrip) ∩ P.capDisk b = P.capRimSet b := by
  have hcapEnd : P.capDisk b ⊆ P.endDisks := by
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  ext y
  constructor
  · rintro ⟨hy, z, hz, rfl⟩
    exact ⟨z, ⟨(P.protected_frontier_iff hcut hsmall z (cap_source_subset b hz)).mp hy.1,
      hz.2⟩, rfl⟩
  · intro hy
    have hcap := P.capRimSet_subset_capDisk b hy
    have hend := hcapEnd hcap
    rw [← P.closedStrip_sdiff_openStrip] at hend
    exact ⟨⟨P.capRimSet_subset_frontier_mark hcut hsmall b hy, hend.2⟩, hcap⟩

end PoincareConjecture.M76.OriginalDiskProduct
