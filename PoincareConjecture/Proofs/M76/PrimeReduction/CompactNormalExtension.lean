import PoincareConjecture.Proofs.M76.PrimeReduction.CompactHalfNormalExtension









set_option autoImplicit false

open Set Geometry

namespace Set

local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1
local notation "I-" => Icc (-1 : ℝ) 0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsFinitePLBallPair.exists_compact_normal_extension
    {s q : Set E} (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (e : s ≃ₜ s) (he : e.IsFinitePL)
    (hfix : ∀ x : s, (x : E) ∈ q → e x = x) :
    ∃ H : (s ×ˢ I : Set (E × ℝ)) ≃ₜ (s ×ˢ I), H.IsFinitePL ∧
      (∀ x : s, (H ⟨((x : E), 0), x.property, by norm_num, zero_le_one⟩ : E × ℝ) =
        ((e x : E), 0)) ∧
      (∀ x : (s ×ˢ I : Set (E × ℝ)),
        (x : E × ℝ).1 ∈ q ∨ (x : E × ℝ).2 = -1 ∨ (x : E × ℝ).2 = 1 → H x = x) ∧
      ∀ x : (s ×ˢ I : Set (E × ℝ)),
        (H x : E × ℝ).2 = 0 ↔ (x : E × ℝ).2 = 0 := by
  obtain ⟨P, hP, hPzero, hPfix, hPiff⟩ :=
    hs.exists_compact_half_normal_extension e he hfix
  let j : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (-(ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hball := hs.prod (isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  have hj : FinitePiecewiseAffineOn j (s ×ˢ I-) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine j⟩
  have hji : InjOn j (s ×ˢ I-) := by
    intro x _ y _ h
    change (x.1, -x.2) = (y.1, -y.2) at h
    have hfirst := congrArg (fun z : E × ℝ => z.1) h
    have hsecond := congrArg (fun z : E × ℝ => z.2) h
    exact Prod.ext hfirst (neg_injective hsecond)
  have hjimage : j '' (s ×ˢ I-) = s ×ˢ I+ := by
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
  have hJinv (x : (s ×ˢ I+ : Set (E × ℝ))) :
      (J.symm x : E × ℝ) = ((x : E × ℝ).1, -(x : E × ℝ).2) := by
    have h := hJval (J.symm x)
    rw [J.apply_symm_apply] at h
    change (x : E × ℝ) = ((J.symm x : E × ℝ).1, -(J.symm x : E × ℝ).2) at h
    refine Prod.ext (congrArg Prod.fst h).symm ?_
    have ht := congrArg Prod.snd h
    dsimp only at ht
    linarith
  let M := J.trans (P.trans J.symm)
  have hM : M.IsFinitePL := hJ.trans (hP.trans hJ.symm)
  have hMval (x : (s ×ˢ I- : Set (E × ℝ))) :
      (M x : E × ℝ) = ((P (J x) : E × ℝ).1, -(P (J x) : E × ℝ).2) :=
    hJinv (P (J x))
  have hMzero (x : s) :
      (M ⟨((x : E), 0), x.property, by norm_num, le_rfl⟩ : E × ℝ) =
        ((e x : E), 0) := by
    have hz : J ⟨((x : E), 0), x.property, by norm_num, le_rfl⟩ =
        ⟨((x : E), 0), x.property, le_rfl, zero_le_one⟩ := by
      apply Subtype.ext
      rw [hJval]
      change ((x : E), -(0 : ℝ)) = ((x : E), 0)
      rw [neg_zero]
    rw [hMval, hz, hPzero]
    simp only [neg_zero]
  have hMiff (x : (s ×ˢ I- : Set (E × ℝ))) :
      (M x : E × ℝ).2 = 0 ↔ (x : E × ℝ).2 = 0 := by
    rw [hMval]
    change -(P (J x) : E × ℝ).2 = 0 ↔ _
    rw [neg_eq_zero, hPiff, hJval]
    change -(x : E × ℝ).2 = 0 ↔ _
    exact neg_eq_zero
  have hMfix (x : (s ×ˢ I- : Set (E × ℝ)))
      (hx : (x : E × ℝ).1 ∈ q ∨ (x : E × ℝ).2 = -1) : M x = x := by
    have hJx : (J x : E × ℝ).1 ∈ q ∨ (J x : E × ℝ).2 = 1 := by
      rw [hJval]
      change (x : E × ℝ).1 ∈ q ∨ -(x : E × ℝ).2 = 1
      exact hx.elim Or.inl (fun h => Or.inr (by rw [h]; norm_num))
    change J.symm (P (J x)) = x
    rw [hPfix _ hJx, J.symm_apply_apply]
  have hmeet (x : (s ×ˢ I- : Set (E × ℝ))) :
      (x : E × ℝ) ∈ s ×ˢ I+ ↔ (x : E × ℝ).2 = 0 := by
    constructor
    · exact fun h => le_antisymm x.property.2.2 h.2.1
    · intro h
      exact ⟨x.property.1, by rw [h]; exact ⟨le_rfl, zero_le_one⟩⟩
  have hoverlap (x : (s ×ˢ I- : Set (E × ℝ))) :
      (x : E × ℝ) ∈ s ×ˢ I+ ↔ (M x : E × ℝ) ∈ s ×ˢ I+ := by
    rw [hmeet, hmeet, hMiff]
  have hagree (x : E × ℝ) (hxM : x ∈ s ×ˢ I-) (hxP : x ∈ s ×ˢ I+) :
      (M ⟨x, hxM⟩ : E × ℝ) = P ⟨x, hxP⟩ := by
    have ht : x.2 = 0 := le_antisymm hxM.2.2 hxP.2.1
    have heM : (⟨x, hxM⟩ : (s ×ˢ I- : Set (E × ℝ))) =
        ⟨(x.1, 0), hxM.1, by norm_num, le_rfl⟩ := Subtype.ext (Prod.ext rfl ht)
    have heP : (⟨x, hxP⟩ : (s ×ˢ I+ : Set (E × ℝ))) =
        ⟨(x.1, 0), hxP.1, le_rfl, zero_le_one⟩ := Subtype.ext (Prod.ext rfl ht)
    rw [heM, heP]
    exact (hMzero ⟨x.1, hxM.1⟩).trans (hPzero ⟨x.1, hxP.1⟩).symm
  obtain ⟨G, hG, hGM, hGP⟩ := Homeomorph.exists_union_finitePL M P hM hP hoverlap hagree
  have hsource : (s ×ˢ I-) ∪ (s ×ˢ I+) = s ×ˢ I := by
    ext x
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, h.2.2.trans zero_le_one⟩
      · exact ⟨h.1, (by linarith [h.2.1]), h.2.2⟩
    · intro h
      exact (le_total x.2 0).elim
        (fun ht => Or.inl ⟨h.1, h.2.1, ht⟩) (fun ht => Or.inr ⟨h.1, ht, h.2.2⟩)
  let H := (Homeomorph.setCongr hsource.symm).trans (G.trans (Homeomorph.setCongr hsource))
  have hH : H.IsFinitePL := hG.setCongr hsource hsource
  have hHM (x : (s ×ˢ I- : Set (E × ℝ))) :
      (H ⟨x, x.property.1, x.property.2.1, x.property.2.2.trans zero_le_one⟩ : E × ℝ) =
        M x := hGM x
  have hHP (x : (s ×ˢ I+ : Set (E × ℝ))) :
      (H ⟨x, x.property.1, by linarith [x.property.2.1], x.property.2.2⟩ : E × ℝ) =
        P x := hGP x
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro x
    exact (hHP ⟨((x : E), 0), x.property, le_rfl, zero_le_one⟩).trans (hPzero x)
  · intro x hx
    apply Subtype.ext
    rcases le_total (x : E × ℝ).2 0 with ht | ht
    · let y : (s ×ˢ I- : Set (E × ℝ)) := ⟨x, x.property.1, x.property.2.1, ht⟩
      have hy : (y : E × ℝ).1 ∈ q ∨ (y : E × ℝ).2 = -1 := by
        rcases hx with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · linarith
      exact (hHM y).trans (congrArg Subtype.val (hMfix y hy))
    · let y : (s ×ˢ I+ : Set (E × ℝ)) := ⟨x, x.property.1, ht, x.property.2.2⟩
      have hy : (y : E × ℝ).1 ∈ q ∨ (y : E × ℝ).2 = 1 := by
        rcases hx with h | h | h
        · exact Or.inl h
        · linarith
        · exact Or.inr h
      exact (hHP y).trans (congrArg Subtype.val (hPfix y hy))
  · intro x
    rcases le_total (x : E × ℝ).2 0 with ht | ht
    · let y : (s ×ˢ I- : Set (E × ℝ)) := ⟨x, x.property.1, x.property.2.1, ht⟩
      have hv := congrArg Prod.snd (hHM y)
      exact hv ▸ hMiff y
    · let y : (s ×ˢ I+ : Set (E × ℝ)) := ⟨x, x.property.1, ht, x.property.2.2⟩
      have hv := congrArg Prod.snd (hHP y)
      exact hv ▸ hPiff y

end Set
