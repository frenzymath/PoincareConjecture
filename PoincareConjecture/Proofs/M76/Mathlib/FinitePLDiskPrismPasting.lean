import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskPrismExtension

set_option autoImplicit false

open Set Geometry

namespace Set

local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1
local notation "I-" => Icc (-1 : ℝ) 0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_two_sided_disk_prism
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
      ∀ (x : E × ℝ) (hx : x ∈ B ×ˢ I-),
        (H ⟨x, ⟨hx.1, hx.2.1, hx.2.2.trans zero_le_one⟩⟩ : E) =
          M ⟨(x.1, -x.2), ⟨hx.1, neg_nonneg.mpr hx.2.2,
            by linarith [hx.2.1]⟩⟩ := by
  classical
  let j : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (-(ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hball := hB.prod (isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  have hj : FinitePiecewiseAffineOn j (B ×ˢ I-) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine j⟩
  have hji : InjOn j (B ×ˢ I-) := by
    intro x _ y _ he
    change (x.1, -x.2) = (y.1, -y.2) at he
    have hfirst := congrArg (fun z : E × ℝ => z.1) he
    have hsecond := congrArg (fun z : E × ℝ => z.2) he
    exact Prod.ext hfirst (neg_injective hsecond)
  have hjimage : j '' (B ×ˢ I-) = B ×ˢ I+ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hy.1, ?_⟩
      change -y.2 ∈ I+
      constructor <;> linarith [hy.2.1, hy.2.2]
    · rintro ⟨hx, ht⟩
      refine ⟨(x.1, -x.2), ⟨hx, ?_⟩, ?_⟩
      · constructor <;> linarith [ht.1, ht.2]
      · change (x.1, - -x.2) = x
        simp only [neg_neg, Prod.mk.eta]
  have hjex := hj.exists_homeomorph_image hji
  rw [hjimage] at hjex
  obtain ⟨J, hJ, hJval⟩ := hjex
  let M' := J.trans M
  have hM' : M'.IsFinitePL := hJ.trans hM
  have hM'0 (x : E) (hx : x ∈ B) :
      (M' ⟨(x, 0), ⟨hx, by norm_num, le_rfl⟩⟩ : E) = x := by
    have he : J ⟨(x, 0), ⟨hx, by norm_num, le_rfl⟩⟩ =
        ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ := by
      apply Subtype.ext
      rw [hJval]
      change (x, -(0 : ℝ)) = (x, 0)
      rw [neg_zero]
    change (M (J _) : E) = x
    rw [he]
    exact hM0 x hx
  have hM'B (x : (B ×ˢ I- : Set (E × ℝ))) :
      (M' x : E) ∈ B ↔ (x : E × ℝ).2 = 0 := by
    constructor
    · intro hxB
      have he : M' ⟨((M' x : E), 0), ⟨hxB, by norm_num, le_rfl⟩⟩ = M' x :=
        Subtype.ext (hM'0 (M' x) hxB)
      exact (congrArg (fun z : (B ×ˢ I- : Set (E × ℝ)) => (z : E × ℝ).2)
        (M'.injective he)).symm
    · intro ht
      have he : x = ⟨((x : E × ℝ).1, 0), ⟨x.property.1, by norm_num, le_rfl⟩⟩ :=
        Subtype.ext (Prod.ext rfl ht)
      have hv : (M' x : E) = (x : E × ℝ).1 := by
        rw [he]
        exact hM'0 _ x.property.1
      exact hv.symm ▸ x.property.1
  have hoverlap (x : (B ×ˢ I- : Set (E × ℝ))) :
      (x : E × ℝ) ∈ B ×ˢ I+ ↔ (M' x : E) ∈ Np := by
    have hx0 : (x : E × ℝ) ∈ B ×ˢ I+ ↔ (x : E × ℝ).2 = 0 := by
      constructor
      · exact fun h => le_antisymm x.property.2.2 h.2.1
      · intro h
        exact ⟨x.property.1, by rw [h]; exact ⟨le_rfl, zero_le_one⟩⟩
    rw [hx0, ← hM'B]
    constructor
    · exact fun h => (hmeet.symm.subset h).2
    · exact fun h => hmeet.subset ⟨(M' x).property, h⟩
  have hagree (x : E × ℝ) (hxM : x ∈ B ×ˢ I-) (hxP : x ∈ B ×ˢ I+) :
      (M' ⟨x, hxM⟩ : E) = P ⟨x, hxP⟩ := by
    have ht : x.2 = 0 := le_antisymm hxM.2.2 hxP.2.1
    have hx : x = (x.1, 0) := Prod.ext rfl ht
    have heM : (⟨x, hxM⟩ : (B ×ˢ I- : Set (E × ℝ))) =
        ⟨(x.1, 0), ⟨hxM.1, by norm_num, le_rfl⟩⟩ := Subtype.ext hx
    have heP : (⟨x, hxP⟩ : (B ×ˢ I+ : Set (E × ℝ))) =
        ⟨(x.1, 0), ⟨hxP.1, le_rfl, zero_le_one⟩⟩ := Subtype.ext hx
    rw [heM, heP]
    exact (hM'0 x.1 hxM.1).trans (hP0 x.1 hxP.1).symm
  obtain ⟨G, hG, hGM, hGP⟩ := Homeomorph.exists_union_finitePL M' P hM' hP hoverlap hagree
  have hsource : (B ×ˢ I-) ∪ (B ×ˢ I+) = B ×ˢ I := by
    ext x
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, h.2.2.trans zero_le_one⟩
      · exact ⟨h.1, (by linarith [h.2.1]), h.2.2⟩
    · intro h
      exact (le_total x.2 0).elim
        (fun ht => Or.inl ⟨h.1, h.2.1, ht⟩) (fun ht => Or.inr ⟨h.1, ht, h.2.2⟩)
  let H := (Homeomorph.setCongr hsource.symm).trans (G.trans (Homeomorph.setCongr hcover))
  have hH : H.IsFinitePL := hG.setCongr hsource hcover
  refine ⟨H, hH, fun x hx => hGP ⟨x, hx⟩, ?_⟩
  intro x hx
  have he : J ⟨x, hx⟩ =
      ⟨(x.1, -x.2), ⟨hx.1, neg_nonneg.mpr hx.2.2,
        by linarith [hx.2.1]⟩⟩ := Subtype.ext (hJval _)
  have hkeep : (H ⟨x, ⟨hx.1, hx.2.1, hx.2.2.trans zero_le_one⟩⟩ : E) = M' ⟨x, hx⟩ :=
    hGM ⟨x, hx⟩
  rw [hkeep]
  change (M (J ⟨x, hx⟩) : E) = _
  rw [he]

end Set
