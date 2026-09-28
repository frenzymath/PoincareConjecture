import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskPrismPasting

set_option autoImplicit false

open Set Geometry

namespace Set

local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1
local notation "I-" => Icc (-1 : ℝ) 0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_two_sided_disk_prism_signed
    {B q N Nm Np : Set E} (hB : IsFinitePLBallPair (ℝ × ℝ) B q)
    (M : (B ×ˢ I+ : Set (E × ℝ)) ≃ₜ Nm)
    (P : (B ×ˢ I+ : Set (E × ℝ)) ≃ₜ Np)
    (hM : M.IsFinitePL) (hP : P.IsFinitePL)
    (hM0 : ∀ (x : E) (hx : x ∈ B),
      (M ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x)
    (hP0 : ∀ (x : E) (hx : x ∈ B),
      (P ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x)
    (hmeet : Nm ∩ Np = B) (hcover : Nm ∪ Np = N) :
    ∃ H : (B ×ˢ I : Set (E × ℝ)) ≃ₜ N, H.IsFinitePL ∧
      (∀ (x : E × ℝ) (hx : x ∈ B ×ˢ I+),
        (H ⟨x, ⟨hx.1, (by linarith [hx.2.1]), hx.2.2⟩⟩ : E) = P ⟨x, hx⟩) ∧
      (∀ (x : E × ℝ) (hx : x ∈ B ×ˢ I-),
        (H ⟨x, ⟨hx.1, hx.2.1, hx.2.2.trans zero_le_one⟩⟩ : E) =
          M ⟨(x.1, -x.2), ⟨hx.1, neg_nonneg.mpr hx.2.2,
            by linarith [hx.2.1]⟩⟩) ∧
      (∀ (x : E) (hx : x ∈ B),
        (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x) ∧
      (∀ x : (B ×ˢ I : Set (E × ℝ)),
        (H x : E) ∈ Np ↔ 0 ≤ (x : E × ℝ).2) ∧
      ∀ x : (B ×ˢ I : Set (E × ℝ)),
        (H x : E) ∈ Nm ↔ (x : E × ℝ).2 ≤ 0 := by
  obtain ⟨H, hH, hkeepP, hkeepM⟩ :=
    hB.exists_two_sided_disk_prism M P hM hP hM0 hP0 hmeet hcover
  have hcenter (x : E) (hx : x ∈ B) :
      (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x :=
    (hkeepP (x, 0) ⟨hx, le_rfl, zero_le_one⟩).trans (hP0 x hx)
  have hpositive (x : (B ×ˢ I : Set (E × ℝ)))
      (ht : 0 ≤ (x : E × ℝ).2) : (H x : E) ∈ Np := by
    have hx : (x : E × ℝ) ∈ B ×ˢ I+ := ⟨x.property.1, ht, x.property.2.2⟩
    have he : (H x : E) = P ⟨x, hx⟩ := hkeepP x hx
    exact he.symm ▸ (P ⟨x, hx⟩).property
  have hnegative (x : (B ×ˢ I : Set (E × ℝ)))
      (ht : (x : E × ℝ).2 ≤ 0) : (H x : E) ∈ Nm := by
    have hx : (x : E × ℝ) ∈ B ×ˢ I- := ⟨x.property.1, x.property.2.1, ht⟩
    have he := hkeepM x hx
    exact he.symm ▸ (M ⟨((x : E × ℝ).1, -(x : E × ℝ).2),
      ⟨x.property.1, neg_nonneg.mpr ht, by linarith [x.property.2.1]⟩⟩).property
  have hbase (x : (B ×ˢ I : Set (E × ℝ)))
      (hx : (H x : E) ∈ B) : (x : E × ℝ).2 = 0 := by
    have he : H ⟨((H x : E), 0), ⟨hx, by norm_num, zero_le_one⟩⟩ = H x :=
      Subtype.ext (hcenter (H x) hx)
    exact (congrArg (fun z : (B ×ˢ I : Set (E × ℝ)) ↦ (z : E × ℝ).2)
      (H.injective he)).symm
  refine ⟨H, hH, hkeepP, hkeepM, hcenter, ?_, ?_⟩
  · intro x
    refine ⟨?_, hpositive x⟩
    intro hx
    by_contra ht
    have hz := hbase x (hmeet.subset ⟨hnegative x (lt_of_not_ge ht).le, hx⟩)
    exact ht (by rw [hz])
  · intro x
    refine ⟨?_, hnegative x⟩
    intro hx
    by_contra ht
    have hz := hbase x (hmeet.subset ⟨hx, hpositive x (lt_of_not_ge ht).le⟩)
    exact ht (by rw [hz])

end Set
