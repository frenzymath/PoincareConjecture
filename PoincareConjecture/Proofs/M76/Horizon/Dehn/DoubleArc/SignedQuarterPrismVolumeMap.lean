import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterPrismPrescribedMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterBoundaryMaps









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_signed_sector_volume_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (signs : Fin 2 → Bool) (α β : ℝ) (hαβ : α < β)
    (F : Fin 2 → Set E) (Q : Bool → Set E) (Z N S rim : Set E)
    (hBall : IsFinitePLBallPair V3 N S)
    (hDisk : IsFinitePLBallPair P2 ((F 0 ∪ F 1) ∪ (Q false ∪ Q true)) rim)
    (hSub : (F 0 ∪ F 1) ∪ (Q false ∪ Q true) ⊆ S)
    (hOut : (S \ ((F 0 ∪ F 1) ∪ (Q false ∪ Q true))).Nonempty)
    (f : ∀ i, ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc α β) ≃ₜ F i)
    (e : ∀ j, signedTubeQuarter (signs 0) (signs 1) ≃ₜ Q j)
    (hf : ∀ i, (f i).IsFinitePL) (he : ∀ j, (e j).IsFinitePL)
    (hinter : F 0 ∩ F 1 = Z) (hdisj : Disjoint (Q false) (Q true))
    (z : Icc α β → E)
    (haxis : ∀ x : ↥(signedTubeRadius 0 (signs 1) ×ˢ Icc α β),
      (x : P2 × ℝ).1 = (0, 0) ↔ (f 0 x : E) ∈ Z)
    (hz : ∀ i (t : Icc α β),
      (f i ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) = z t)
    (hcontact : ∀ j i (x : signedTubeQuarter (signs 0) (signs 1)),
      (e j x : E) ∈ F i ↔ (x : P2) ∈ signedTubeRadius i (signs i.rev))
    (hkeep : ∀ i j (x : signedTubeRadius i (signs i.rev)),
      (f i ⟨(x, if j then β else α), x.property,
        by cases j <;> simp [hαβ.le]⟩ : E) =
          e j ⟨x, signedTubeRadius_subset_quarter signs i x.property⟩) :
    ∃ H : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc α β) ≃ₜ N,
      H.IsFinitePL ∧
      (∀ i (x : ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc α β)),
        (H ⟨x, signedTubeRadius_subset_quarter signs i x.property.1, x.property.2⟩ : E) = f i x) ∧
      (∀ j (x : signedTubeQuarter (signs 0) (signs 1)),
        (H ⟨(x, if j then β else α), x.property, by cases j <;> simp [hαβ.le]⟩ : E) = e j x) ∧
      ∀ x : ↥(signedTubeQuarter (signs 0) (signs 1) ×ˢ Icc α β),
        (x : P2 × ℝ) ∈
          (signedTubeOuterArc (signs 0) (signs 1) ×ˢ Icc α β) ∪
            signedTubeSectorPrescribed (signs 0) (signs 1) α β ↔ (H x : E) ∈ S := by
  classical
  let D := (F 0 ∪ F 1) ∪ (Q false ∪ Q true)
  let complement := S \ (D \ rim)
  obtain ⟨p, hp, hpf, hpe⟩ := exists_signed_sector_prescribed_map
    signs α β hαβ F Q Z f e hf he hinter hdisj z haxis hz hcontact hkeep
  obtain ⟨hSource, hOuter, hPrescribed, hSourceMeet⟩ :=
    signedTubeSector_boundary_disks (signs 0) (signs 1) α β hαβ
  have hComplement : IsFinitePLBallPair P2 complement rim :=
    hBall.boundary_disk_complement (by simp) hDisk hSub hOut
  have hTargetUnion : complement ∪ D = S := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hSub hx
    · intro hx
      by_cases hd : x ∈ D
      · exact Or.inr hd
      · exact Or.inl ⟨hx, fun h => hd h.1⟩
  have hTargetMeet : complement ∩ D = rim := by
    ext x
    constructor
    · rintro ⟨hxC, hxD⟩
      by_contra hr
      exact hxC.2 ⟨hxD, hr⟩
    · intro hx
      exact ⟨⟨hSub (hDisk.1 hx), fun h => h.2 hx⟩, hDisk.1 hx⟩
  have hrim (x : signedTubeSectorPrescribed (signs 0) (signs 1) α β) :
      (x : P2 × ℝ) ∈ signedTubeSectorRim (signs 0) (signs 1) α β ↔ (p x : E) ∈ rim :=
    finitePL_ball_boundary_iff hPrescribed hDisk p hp x
  obtain ⟨b, hb, hbkeep, _, _⟩ := hOuter.exists_union_homeomorph_of_boundary_piece
    hComplement hSourceMeet hTargetMeet p hp hrim
  have hTarget : IsFinitePLBallPair V3 N (complement ∪ D) := hTargetUnion.symm ▸ hBall
  obtain ⟨H, hH, hHb, hHboundary⟩ := hSource.exists_extension hTarget b hb
  have hHkeep (x : signedTubeSectorPrescribed (signs 0) (signs 1) α β) :
      (H ⟨x, hSource.1 (Or.inr x.property)⟩ : E) = p x :=
    (congrArg Subtype.val (hHb ⟨x, Or.inr x.property⟩)).trans
      (congrArg Subtype.val (hbkeep x))
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro i x
    exact (hHkeep ⟨x, Or.inl ⟨signedTubeRadius_subset_radialRim signs i x.property.1,
      x.property.2⟩⟩).trans (hpf i x)
  · intro j x
    exact (hHkeep ⟨(x, if j then β else α), Or.inr ⟨x.property,
      by cases j <;> simp⟩⟩).trans (hpe j x)
  · intro x
    simpa only [hTargetUnion] using hHboundary x

end PoincareConjecture.M76.Dehn
