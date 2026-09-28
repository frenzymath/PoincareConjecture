import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcExtension
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalStripDiskAttachment
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripHalfDiskComplement



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)

theorem exists_cut_disk_enlargement_across_half_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T Q D B : Set E} (hT : IsFinitePLBallPair P2 T Q)
    (c : P2 → E) (positive : Bool)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcT : MapsTo c source T)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hB : IsFinitePLBallPair P2 B ((B ∩ Q) ∪ c '' arm 0))
    (hcover : D ∪ B = T) (hinter : D ∩ B = c '' arm 0)
    (hhalf : c '' halfSource positive ⊆ B) :
    let Z := c '' arm (farArmParameter positive)
    ∃ D' B' U' V' : Set E,
      IsFinitePLBallPair P2 D' (Z ∪ U') ∧
      IsFinitePLBallPair P2 B' (Z ∪ V') ∧
      IsFinitePLBallPair ℝ U' {c (0, farArmParameter positive), c (1, farArmParameter positive)} ∧
      IsFinitePLBallPair ℝ V' {c (0, farArmParameter positive), c (1, farArmParameter positive)} ∧
      D' ∪ B' = T ∧ D' ∩ B' = Z ∧
      D' ∩ Q = U' ∧ B' ∩ Q = V' ∧
      D ⊆ D' ∧ D' ⊆ D ∪ c '' halfSource positive ∧ B' ⊆ B ∧
      Disjoint B' (c '' arm 0) ∧ Disjoint Z (c '' arm 0) ∧
      c '' arm 0 ⊆ D' \ B' ∧ D' = D ∪ c '' halfSource positive ∧
      B' = B \ ((c '' halfSource positive) \ Z) := by
  let H := c '' halfSource positive
  let Z := c '' arm (farArmParameter positive)
  let C := B \ (H \ Z)
  obtain ⟨hC, hHC, hHi, hCcenter, hZ⟩ :=
    half_strip_disk_complement hB c positive hcPL hci hcQ hhalf rfl
  have hV : ∃ V : Set E,
      IsFinitePLBallPair ℝ V {c (0, farArmParameter positive), c (1, farArmParameter positive)} ∧
      IsFinitePLBallPair P2 C (Z ∪ V) ∧ H ∪ C = B ∧ H ∩ C = Z ∧
      C ∩ ((B ∩ Q) ∪ c '' arm 0) = V := by
    cases positive with
    | false => exact exists_lower_half_strip_complement hB c hcPL hci hcQ hhalf rfl
    | true => exact exists_upper_half_strip_complement hB c hcPL hci hcQ hhalf rfl
  obtain ⟨V, hV, hCV, _, _, hcontact⟩ := hV
  have hCQ : C ∩ Q = V := by
    rw [← hcontact]
    ext x
    constructor
    · exact fun hx ↦ ⟨hx.1, Or.inl ⟨hx.1.1, hx.2⟩⟩
    · rintro ⟨hxC, ⟨_, hxQ⟩ | hxcenter⟩
      · exact ⟨hxC, hxQ⟩
      · exact (Set.disjoint_left.mp hCcenter hxC hxcenter).elim
  have hVT : V ⊆ Q := hCQ.symm.subset.trans inter_subset_right
  have hCT : C ⊆ T := fun _ hx ↦ hcover.subset (Or.inr hx.1)
  have hZends : c (0, farArmParameter positive) ≠ c (1, farArmParameter positive) := by
    intro heq
    have h0 : (0, farArmParameter positive) ∈ arm (farArmParameter positive) :=
      ⟨by norm_num, rfl⟩
    have h1 : (1, farArmParameter positive) ∈ arm (farArmParameter positive) :=
      ⟨by norm_num, rfl⟩
    have h := hci (arm_far_subset_source positive h0)
      (arm_far_subset_source positive h1) heq
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst h
    norm_num at h01
  have hZproper : Z \ {c (0, farArmParameter positive), c (1, farArmParameter positive)} ⊆ T \ Q := by
    rintro y ⟨⟨x, hx, rfl⟩, hnot⟩
    refine ⟨hcT (arm_far_subset_source positive hx), ?_⟩
    intro hxQ
    rcases (hcQ x (arm_far_subset_source positive hx)).mp hxQ with ht | ht
    · exact hnot (Or.inl (congrArg c (Prod.ext ht hx.2)))
    · exact hnot (Or.inr (congrArg c (Prod.ext ht hx.2)))
  have hCV' : IsFinitePLBallPair P2 C (V ∪ Z) := by simpa only [union_comm] using hCV
  obtain ⟨U, hU, _, _, hnew, hwhole, hcommon, _, houter⟩ :=
    hT.exists_boundary_attached_disk_complement hCV' hCT hV hVT hZ hZends hZproper
  let N := T \ (C \ Z)
  have hDN : D ⊆ N := by
    intro x hxD
    refine ⟨hcover.subset (Or.inl hxD), ?_⟩
    rintro ⟨hxC, _⟩
    exact Set.disjoint_left.mp hCcenter hxC (hinter.subset ⟨hxD, hxC.1⟩)
  have hNsmall : N ⊆ D ∪ H := by
    intro x hxN
    rcases hcover.superset hxN.1 with hxD | hxB
    · exact Or.inl hxD
    · by_cases hxH : x ∈ H
      · exact Or.inr hxH
      · have hxC : x ∈ C := ⟨hxB, fun hx ↦ hxH hx.1⟩
        have hxZ : x ∈ Z := by_contra fun hn ↦ hxN.2 ⟨hxC, hn⟩
        exact (hxH ((hHi : H ∩ C = Z).superset hxZ).1).elim
  have hZcenter : Disjoint Z (c '' arm 0) := (disjoint_center_far_images c hci positive).symm
  have hHN : H ⊆ N := by
    intro x hx
    refine ⟨hcover.subset (Or.inr (hhalf hx)), ?_⟩
    rintro ⟨hxC, hxZ⟩
    exact hxZ (hHi.subset ⟨hx, hxC⟩)
  refine ⟨N, C, U, V, hnew, hCV, hU, hV, ?_, ?_, houter, hCQ,
    hDN, hNsmall, fun _ hx ↦ hx.1, hCcenter, hZcenter, ?_,
    Subset.antisymm hNsmall (union_subset hDN hHN), rfl⟩
  · simpa only [union_comm] using hwhole
  · simpa only [inter_comm] using hcommon
  · intro x hx
    exact ⟨hDN ((hinter.superset hx).1), fun hxC ↦ Set.disjoint_left.mp hCcenter hxC hx⟩

end PoincareConjecture.M76.Dehn.Annuli
