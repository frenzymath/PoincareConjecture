import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanCorner













noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture






theorem m64Intrinsic_two_arc_frontier_germ
    (H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (c : AffineBasis (Fin 3) ℝ AnnulusCoordinates) (hc : c 0 ∈ H.source)
    {α β : ℝ → AnnulusCoordinates} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hiα : InjOn α (Icc 0 A)) (hiβ : InjOn β (Icc 0 B))
    (haxisα : ∀ s : ℝ, H (AffineMap.lineMap (c 0) (c 1) s) = α s)
    (haxisβ : ∀ s : ℝ, H (AffineMap.lineMap (c 0) (c 2) s) = β s)
    {W C : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : H (c 0) ∉ W)
    (hC : C = (α '' Icc 0 A) ∪ (β '' Icc 0 B) ∪ W) :
    ∀ᶠ z in 𝓝 (c 0), H z ∈ C ↔
      (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0) := by
  obtain ⟨δ, hδ, hbox⟩ := Topology.Surface.exists_pos_coordinate_box_subset c
    (H.open_source.mem_nhds hc)
  let η := min (A / 2) (min (B / 2) (δ / 2))
  have hη : 0 < η := lt_min (half_pos hA) (lt_min (half_pos hB) (half_pos hδ))
  have hηA : η ≤ A := (min_le_left _ _).trans (half_le_self hA.le)
  have hηB : η ≤ B := ((min_le_right _ _).trans (min_le_left _ _)).trans
    (half_le_self hB.le)
  have hηδ : η < δ := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hδ)
  have hsourceα {s : ℝ} (hs : s ∈ Icc 0 η) :
      AffineMap.lineMap (c 0) (c 1) s ∈ H.source := by
    apply hbox
    have hsδ : s < δ := hs.2.trans_lt hηδ
    simpa [Topology.Surface.coordinateBox, AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring] using
        (show (-δ < s ∧ s < δ) ∧ (-δ < (0 : ℝ) ∧ 0 < δ) from
          ⟨⟨by linarith [hs.1], hsδ⟩, ⟨by linarith, hδ⟩⟩)
  have hsourceβ {s : ℝ} (hs : s ∈ Icc 0 η) :
      AffineMap.lineMap (c 0) (c 2) s ∈ H.source := by
    apply hbox
    have hsδ : s < δ := hs.2.trans_lt hηδ
    simpa [Topology.Surface.coordinateBox, AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring] using
        (show (-δ < (0 : ℝ) ∧ 0 < δ) ∧ (-δ < s ∧ s < δ) from
          ⟨⟨by linarith, hδ⟩, ⟨by linarith [hs.1], hsδ⟩⟩)
  have hα0 : α 0 = H (c 0) := by simpa using (haxisα 0).symm
  have hβ0 : β 0 = H (c 0) := by simpa using (haxisβ 0).symm
  let T := W ∪ (α '' Icc η A) ∪ (β '' Icc η B)
  have hT : IsCompact T :=
    (hW.union (isCompact_Icc.image_of_continuousOn (hα.mono
      (Icc_subset_Icc hη.le le_rfl)))).union
        (isCompact_Icc.image_of_continuousOn (hβ.mono (Icc_subset_Icc hη.le le_rfl)))
  have hpT : H (c 0) ∉ T := by
    rintro ((hp | ⟨s, hs, heq⟩) | ⟨s, hs, heq⟩)
    · exact hpW hp
    · have hs0 : s = 0 := hiα ⟨hη.le.trans hs.1, hs.2⟩ ⟨le_rfl, hA.le⟩
        (heq.trans hα0.symm)
      linarith [hs.1]
    · have hs0 : s = 0 := hiβ ⟨hη.le.trans hs.1, hs.2⟩ ⟨le_rfl, hB.le⟩
        (heq.trans hβ0.symm)
      linarith [hs.1]
  have havoid : ∀ᶠ z in 𝓝 (c 0), H z ∉ T :=
    (H.continuousAt hc).eventually (hT.isClosed.isOpen_compl.mem_nhds hpT)
  filter_upwards [havoid, H.open_source.mem_nhds hc,
    Topology.Surface.coordinateBox_mem_nhds c hη] with z hzT hzH hzbox
  constructor
  · intro hzC
    rw [hC] at hzC
    rcases hzC with (⟨s, hs, heq⟩ | ⟨s, hs, heq⟩) | hzW
    · have hsη : s < η := by
        by_contra hn
        exact hzT (Or.inl (Or.inr ⟨s, ⟨le_of_not_gt hn, hs.2⟩, heq⟩))
      have hzline : z = AffineMap.lineMap (c 0) (c 1) s :=
        H.injOn hzH (hsourceα ⟨hs.1, hsη.le⟩) (heq.symm.trans (haxisα s).symm)
      right
      rw [hzline]
      simpa [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] using hs.1
    · have hsη : s < η := by
        by_contra hn
        exact hzT (Or.inr ⟨s, ⟨le_of_not_gt hn, hs.2⟩, heq⟩)
      have hzline : z = AffineMap.lineMap (c 0) (c 2) s :=
        H.injOn hzH (hsourceβ ⟨hs.1, hsη.le⟩) (heq.symm.trans (haxisβ s).symm)
      left
      rw [hzline]
      simpa [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] using hs.1
    · exact False.elim (hzT (Or.inl (Or.inl hzW)))
  · intro hzray
    rw [hC]
    rcases hzray with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hzline : z = AffineMap.lineMap (c 0) (c 2) (c.coord 2 z) := by
        calc
          z = c 0 + c.coord 1 z • (c 1 - c 0) + c.coord 2 z • (c 2 - c 0) :=
            (Topology.Surface.affineBasis_coordinate_reconstruction c z).symm
          _ = AffineMap.lineMap (c 0) (c 2) (c.coord 2 z) := by
            rw [h1]
            simp only [zero_smul, add_zero, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
            module
      have hsB : c.coord 2 z ≤ B := hzbox.2.2.le.trans hηB
      exact Or.inl (Or.inr ⟨c.coord 2 z, ⟨h2, hsB⟩, by rw [← haxisβ, ← hzline]⟩)
    · have hzline : z = AffineMap.lineMap (c 0) (c 1) (c.coord 1 z) := by
        calc
          z = c 0 + c.coord 1 z • (c 1 - c 0) + c.coord 2 z • (c 2 - c 0) :=
            (Topology.Surface.affineBasis_coordinate_reconstruction c z).symm
          _ = AffineMap.lineMap (c 0) (c 1) (c.coord 1 z) := by
            rw [h2]
            simp only [zero_smul, add_zero, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
            module
      have hsA : c.coord 1 z ≤ A := hzbox.1.2.le.trans hηA
      exact Or.inl (Or.inl ⟨c.coord 1 z, ⟨h1, hsA⟩, by rw [← haxisα, ← hzline]⟩)

end PoincareConjecture
