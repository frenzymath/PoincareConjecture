import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskSideBand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryBandComplement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement

set_option autoImplicit false

open Set Geometry

namespace Set

local notation "I" => Icc (0 : ℝ) 1
local notation "P2" => (ℝ × ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_disk_prism_extension
    {N S B q : Set E} (hN : IsFinitePLBallPair V N S)
    (hB : IsFinitePLBallPair P2 B q) (hBS : B ⊆ S) (hout : (S \ B).Nonempty)
    (F : E × ℝ → E) (hF : FinitePiecewiseAffineOn F (q ×ˢ I))
    (hi : InjOn F (q ×ˢ I)) (hinside : MapsTo F (q ×ˢ I) S)
    (hzero : ∀ x ∈ q, F (x, 0) = x)
    (hcontact : ∀ x ∈ q ×ˢ I, F x ∈ B ↔ x.2 = 0) :
    ∃ H : (B ×ˢ I : Set (E × ℝ)) ≃ₜ N, H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ B),
        (H ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x) ∧
      (∀ (x : E × ℝ) (hx : x ∈ q ×ˢ I),
        (H ⟨x, ⟨hB.1 hx.1, hx.2⟩⟩ : E) = F x) ∧
      (∀ x : (B ×ˢ I : Set (E × ℝ)),
        (H x : E) ∈ B ↔ (x : E × ℝ).2 = 0) ∧
      ∀ x : (B ×ˢ I : Set (E × ℝ)),
        (H x : E) ∈ S ↔
          (x : E × ℝ).1 ∈ q ∨ (x : E × ℝ).2 ∈ ({0, 1} : Set ℝ) := by
  classical
  let U := S \ (B \ q)
  let band := F '' (q ×ˢ I)
  let top := F '' (q ×ˢ ({1} : Set ℝ))
  let cap := U \ (band \ top)
  let A : Set (E × ℝ) := (B ×ˢ {(0 : ℝ)}) ∪ (q ×ˢ I)
  have hU : IsFinitePLBallPair P2 U q :=
    hN.boundary_disk_complement (by simp [Module.finrank_prod]) hB hBS hout
  have hbandU : MapsTo F (q ×ˢ I) U := by
    intro x hx
    refine ⟨hinside hx, ?_⟩
    rintro ⟨hxB, hxq⟩
    have ht : x.2 = 0 := (hcontact x hx).mp hxB
    have he : x = (x.1, (0 : ℝ)) := Prod.ext rfl ht
    apply hxq
    rw [he, hzero x.1 hx.1]
    exact hx.1
  have hproper : ∀ x ∈ q ×ˢ I, F x ∈ q ↔ x.2 = 0 := by
    intro x hx
    constructor
    · exact fun hq => (hcontact x hx).mp (hB.1 hq)
    · intro ht
      have he : x = (x.1, (0 : ℝ)) := Prod.ext rfl ht
      rw [he, hzero x.1 hx.1]
      exact hx.1
  obtain ⟨n, P, hPi, _, hPq⟩ := hB.exists_polygon_boundary
  have ha : P 0 ∈ q := hPq ▸ P.vertex_mem_boundary 0
  have hb : P 1 ∈ q := hPq ▸ P.vertex_mem_boundary 1
  have hab : P 0 ≠ P 1 := by
    intro he
    have h := congrArg Fin.val (hPi he)
    norm_num at h
  have hcap : IsFinitePLBallPair P2 cap top :=
    hU.boundary_band_complement ha hb hab F hF hi hbandU hzero hproper
  have htopside : q ×ˢ ({1} : Set ℝ) ⊆ q ×ˢ I := by
    intro x hx
    exact ⟨hx.1, by rw [show x.2 = 1 from hx.2]; exact ⟨zero_le_one, le_rfl⟩⟩
  have htopband : top ⊆ band := image_mono htopside
  have htopU : top ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hbandU (htopside hy)
  have hqband : q ⊆ band := by
    intro x hx
    exact ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩, hzero x hx⟩
  have hbandS : band ⊆ S := by rintro x ⟨y, hy, rfl⟩; exact hinside hy
  have hwhole : cap ∪ (B ∪ band) = S := by
    apply Subset.antisymm
    · rintro x (hx | hx | hx)
      · exact hx.1.1
      · exact hBS hx
      · exact hbandS hx
    · intro x hx
      by_cases hxB : x ∈ B
      · exact Or.inr (Or.inl hxB)
      by_cases hxband : x ∈ band
      · exact Or.inr (Or.inr hxband)
      exact Or.inl ⟨⟨hx, fun h => hxB h.1⟩, fun h => hxband h.1⟩
  have hmeet : cap ∩ (B ∪ band) = top := by
    apply Subset.antisymm
    · rintro x ⟨hxC, hxB | hxband⟩
      · have hxq : x ∈ q := by
          by_contra hn
          exact hxC.1.2 ⟨hxB, hn⟩
        by_contra hn
        exact hxC.2 ⟨hqband hxq, hn⟩
      · by_contra hn
        exact hxC.2 ⟨hxband, hn⟩
    · intro x hx
      exact ⟨⟨htopU hx, fun h => h.2 hx⟩, Or.inr (htopband hx)⟩
  obtain ⟨e, he, hezero, heside, herim⟩ :=
    hB.exists_disk_side_band_map F hF hi hzero hcontact
  have hsource0 := hB.prod (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  have hsourceRim : (q ×ˢ I) ∪ (B ×ˢ ({0, 1} : Set ℝ)) =
      (B ×ˢ ({1} : Set ℝ)) ∪ A := by
    ext x
    simp only [A, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have hsource : IsFinitePLBallPair V (B ×ˢ I)
      ((B ×ˢ ({1} : Set ℝ)) ∪ A) := by rwa [hsourceRim] at hsource0
  have htarget : IsFinitePLBallPair V N (cap ∪ (B ∪ band)) := hwhole.symm ▸ hN
  have hsourceMeet : (B ×ˢ ({1} : Set ℝ)) ∩ A = q ×ˢ ({1} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨hx, hy | hy⟩
      · exact False.elim (zero_ne_one (hy.2.symm.trans hx.2))
      · exact ⟨hy.1, hx.2⟩
    · intro hx
      exact ⟨⟨hB.1 hx.1, hx.2⟩, Or.inr (htopside hx)⟩
  obtain ⟨H, hH, hkeep, houter, hactive⟩ := hsource.exists_extension_of_boundary_piece
    htarget (hB.prod_singleton (1 : ℝ)) hcap hsourceMeet hmeet e he herim
  have hbottom (x : E) (hx : x ∈ B) :
      (H ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x :=
    (congrArg Subtype.val (hkeep ⟨(x, 0), Or.inl ⟨hx, rfl⟩⟩)).trans (hezero x hx)
  have hside (x : E × ℝ) (hx : x ∈ q ×ˢ I) :
      (H ⟨x, ⟨hB.1 hx.1, hx.2⟩⟩ : E) = F x :=
    (congrArg Subtype.val (hkeep ⟨x, Or.inr hx⟩)).trans (heside x hx)
  have hbaseiff (x : (B ×ˢ I : Set (E × ℝ))) :
      (H x : E) ∈ B ↔ (x : E × ℝ).2 = 0 := by
    constructor
    · intro hxB
      have heq : H ⟨((H x : E), 0), ⟨hxB, le_rfl, zero_le_one⟩⟩ = H x :=
        Subtype.ext (hbottom (H x) hxB)
      exact (congrArg (fun z : (B ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).2)
        (H.injective heq)).symm
    · intro ht
      have heq : x = ⟨((x : E × ℝ).1, 0), ⟨x.property.1, le_rfl, zero_le_one⟩⟩ :=
        Subtype.ext (Prod.ext rfl ht)
      have hv : (H x : E) = (x : E × ℝ).1 := by
        rw [heq]
        exact hbottom _ x.property.1
      exact hv.symm ▸ x.property.1
  refine ⟨H, hH, hbottom, hside, hbaseiff, ?_⟩
  intro x
  have hHrim : (x : E × ℝ) ∈ ((B ×ˢ ({1} : Set ℝ)) ∪ A) ↔ (H x : E) ∈ S := by
    rw [← hwhole]
    exact (houter x).or (hactive x)
  rw [← hHrim, ← hsourceRim]
  simp only [mem_union, mem_prod, x.property.1, x.property.2, and_true, true_and]

end Set
