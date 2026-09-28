import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.CapAttachmentCharts
import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereDisks










set_option autoImplicit false

open Set Metric Geometry

private theorem isOpen_relative_of_open_carrier_neighborhood
    {X : Type*} [TopologicalSpace X] {A O U W : Set X}
    (hAO : A ⊆ O) (hOU : O ⊆ U)
    (hA : IsOpen ((Subtype.val : U → X) ⁻¹' A))
    (hO : IsOpen ((Subtype.val : W → X) ⁻¹' O)) :
    IsOpen ((Subtype.val : W → X) ⁻¹' A) := by
  obtain ⟨V, hV, hVA⟩ := isOpen_induced_iff.mp hA
  have heq : A = V ∩ O := by
    ext x
    constructor
    · intro hx
      have hxu := hOU (hAO hx)
      have hh := congrArg (fun T : Set U => (⟨x, hxu⟩ : U) ∈ T) hVA
      exact ⟨(show x ∈ V ↔ x ∈ A from eq_iff_iff.mp hh).mpr hx, hAO hx⟩
    · intro hx
      have hh := congrArg (fun T : Set U => (⟨x, hOU hx.2⟩ : U) ∈ T) hVA
      exact (show x ∈ V ↔ x ∈ A from eq_iff_iff.mp hh).mp hx.1
  rw [heq, preimage_inter]
  exact (hV.preimage continuous_subtype_val).inter hO

namespace Set.IsFinitePLBallPair

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1



theorem exists_boundary_disk_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D B : Set E} (hD : IsFinitePLBallPair V3 D B) {p : E} (hp : p ∈ B) :
    ∃ d q : Set E, IsFinitePLBallPair V2 d q ∧ d ⊆ B ∧
      p ∈ d \ q ∧ IsOpen ((Subtype.val : B → E) ⁻¹' (d \ q)) := by
  obtain ⟨H, hH, hHB⟩ := hD.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨_, L, _, _, hL, hLs⟩ := hD.exists_finite_carrier_and_rim_complexes
  let HB := H.restrictSubsets hD.1 isClosed_closedBall.frontier_subset hHB
  have hB : HB.IsFinitePL :=
    hH.restrictSubsets hD.1 isClosed_closedBall.frontier_subset hHB L hL hLs
  exact hB.exists_local_ball_pairs_of_convex_frontier (isCompact_closedBall _ _)
    (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
    (by simp) ⟨p, hp⟩




theorem exists_local_ball_of_attachment_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D B U W : Set E} (hD : IsFinitePLBallPair V3 D B)
    (H : (B ×ˢ J : Set (E × ℝ)) ≃ₜ U) (hH : H.IsFinitePL) (hUW : U ⊆ W)
    (hbase : ∀ x (hx : x ∈ B),
      (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x)
    (σ : E × ℝ → E) (hσval : ∀ z, (H z : E) = σ z)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ η →
      IsOpen ((Subtype.val : W → E) ⁻¹' (σ '' (B ×ˢ Ioo (-ε) ε))))
    {p : E} (hp : p ∈ B) :
    ∃ d q : Set E, IsFinitePLBallPair (V2 × ℝ) d q ∧ d ⊆ W ∧
      p ∈ d \ q ∧ IsOpen ((Subtype.val : W → E) ⁻¹' (d \ q)) := by
  obtain ⟨b, r, hb, hbB, hpb, hbopen⟩ := hD.exists_boundary_disk_neighborhood hp
  have hσ : FinitePiecewiseAffineOn σ (B ×ˢ J) := by
    obtain ⟨f, hf, hfval⟩ := hH
    exact hf.congr (fun z hz => (hfval ⟨z, hz⟩).symm.trans (hσval ⟨z, hz⟩))
  have hσinj : InjOn σ (B ×ˢ J) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hσval ⟨x, hx⟩).trans (hxy.trans (hσval ⟨y, hy⟩).symm))))
  let ε := η / 2
  have hε : 0 < ε := half_pos hη
  have hεη : ε ≤ η := by dsimp [ε]; linarith
  have hεone : ε ≤ 1 := hεη.trans hηsmall
  let A := b ×ˢ Icc (-ε) ε
  let R := (r ×ˢ Icc (-ε) ε) ∪ (b ×ˢ ({-ε, ε} : Set ℝ))
  have hA : IsFinitePLBallPair (V2 × ℝ) A R :=
    hb.prod (isFinitePLBallPair_Icc (by linarith : -ε < ε))
  have hAB : A ⊆ B ×ˢ J := fun z hz =>
    ⟨hbB hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hσU : MapsTo σ (B ×ˢ J) U :=
    fun z hz => (hσval ⟨z, hz⟩) ▸ (H ⟨z, hz⟩).property
  have hinner : A \ R = (b \ r) ×ˢ Ioo (-ε) ε := by
    ext z
    change (z.1 ∈ b ∧ -ε ≤ z.2 ∧ z.2 ≤ ε) ∧
        ¬((z.1 ∈ r ∧ -ε ≤ z.2 ∧ z.2 ≤ ε) ∨
          (z.1 ∈ b ∧ (z.2 = -ε ∨ z.2 = ε))) ↔
      (z.1 ∈ b ∧ z.1 ∉ r) ∧ -ε < z.2 ∧ z.2 < ε
    constructor
    · rintro ⟨⟨hzb, hl, hu⟩, hn⟩
      refine ⟨⟨hzb, fun hr => hn (Or.inl ⟨hr, hl, hu⟩)⟩, ?_, ?_⟩
      · exact lt_of_le_of_ne hl (fun ht => hn (Or.inr ⟨hzb, Or.inl ht.symm⟩))
      · exact lt_of_le_of_ne hu (fun ht => hn (Or.inr ⟨hzb, Or.inr ht⟩))
    · rintro ⟨⟨hzb, hzr⟩, hl, hu⟩
      refine ⟨⟨hzb, hl.le, hu.le⟩, ?_⟩
      rintro (⟨hr, _⟩ | ⟨_, ht | ht⟩)
      · exact hzr hr
      · linarith
      · linarith
  have himage : σ '' A \ σ '' R = σ '' ((b \ r) ×ˢ Ioo (-ε) ε) := by
    rw [← hinner]
    simpa only [inter_eq_right.mpr hA.1] using
      (Set.InjOn.image_sdiff (t := R) (hσinj.mono hAB)).symm
  have hrel : IsOpen ((Subtype.val : U → E) ⁻¹' (σ '' A \ σ '' R)) := by
    let V : Set (B ×ˢ J : Set (E × ℝ)) :=
      (fun z => (⟨(z : E × ℝ).1, z.property.1⟩ : B)) ⁻¹'
        ((Subtype.val : B → E) ⁻¹' (b \ r)) ∩
      (fun z => (z : E × ℝ).2) ⁻¹' Ioo (-ε) ε
    have hV : IsOpen V :=
      (hbopen.preimage ((continuous_fst.comp continuous_subtype_val).subtype_mk _)).inter
        (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val))
    have heq : H '' V = (Subtype.val : U → E) ⁻¹' (σ '' A \ σ '' R) := by
      rw [himage]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ⟨hz.1, hz.2⟩, (hσval z).symm⟩
      · rintro ⟨z, hz, hzy⟩
        have hzB : z ∈ B ×ˢ J :=
          ⟨hbB hz.1.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
        exact ⟨⟨z, hzB⟩, ⟨hz.1, hz.2⟩, Subtype.ext ((hσval _).trans hzy)⟩
    rw [← heq]
    exact H.isOpenMap V hV
  refine ⟨σ '' A, σ '' R, hA.image_of_subset hσ hAB hσinj,
    (image_subset_iff.mpr (fun z hz => hUW (hσU (hAB hz)))), ?_, ?_⟩
  · rw [himage]
    exact ⟨(p, 0), ⟨hpb, by constructor <;> linarith⟩,
      (hσval ⟨(p, 0), hp, by norm_num, zero_le_one⟩).symm.trans (hbase p hp)⟩
  · apply isOpen_relative_of_open_carrier_neighborhood (U := U)
      (O := σ '' (B ×ˢ Ioo (-ε) ε)) ?_ ?_ hrel (hopen ε hε hεη)
    · rw [himage]
      exact image_mono (prod_mono (sdiff_subset.trans hbB) subset_rfl)
    · rintro _ ⟨z, hz, rfl⟩
      exact hσU ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩

end Set.IsFinitePLBallPair
