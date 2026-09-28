import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismPreimages
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPathFrames
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPaths

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signed_prism_chain_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (B : Fin (n + 2) → Set E) (J : Fin (n + 1) → Set E)
    (G : ∀ e, signedTubeDiamond ≃ₜ J e)
    (map : ∀ i, ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (hcontact : ∀ e : Fin (n + 1), B e.castSucc ∩ B e.succ = J e)
    (hfar : ∀ i j, i.val + 1 < j.val → Disjoint (B i) (B j))
    (hupper : ∀ (e : Fin (n + 1)) (x : signedTubeDiamond),
      (map e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = G e x)
    (hlower : ∀ (e : Fin (n + 1)) (x : signedTubeDiamond),
      (map e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = G e x) :
    ∃ H : ↥(signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) ≃ₜ (⋃ i, B i),
      H.IsFinitePL ∧ ∀ i (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ))),
        (H ⟨x, x.property.1,
          (ht.monotone (Fin.zero_le _)).trans x.property.2.1,
          x.property.2.2.trans (ht.monotone (Fin.le_last _))⟩ : E) = map i x := by
  classical
  let S := fun i : Fin (n + 2) => signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)
  have hordered (i j : Fin (n + 2)) (hij : i < j) :
      (∀ x : S i, (x : P2 × ℝ) ∈ S j ↔ (map i x : E) ∈ B j) ∧
      (∀ x : S j, (x : P2 × ℝ) ∈ S i ↔ (map j x : E) ∈ B i) ∧
      ∀ (x : P2 × ℝ) (hi : x ∈ S i) (hj : x ∈ S j),
        (map i ⟨x, hi⟩ : E) = map j ⟨x, hj⟩ := by
    by_cases hnext : i.val + 1 = j.val
    · obtain ⟨e, hei, hej⟩ : ∃ e : Fin (n + 1), e.castSucc = i ∧ e.succ = j := by
        exact ⟨⟨i.val, by have hj := j.isLt; omega⟩, Fin.ext rfl, Fin.ext hnext⟩
      subst i
      subst j
      have htime : e.castSucc.succ = e.succ.castSucc := Fin.ext rfl
      have hu (x : S e.castSucc) : (map e.castSucc x : E) ∈ J e ↔
          (x : P2 × ℝ).2 = t e.castSucc.succ :=
        signed_prism_end_preimage ⟨(ht Fin.castSucc_lt_succ).le, le_rfl⟩
          (map e.castSucc) (G e) (hupper e) x
      have hl (x : S e.succ) : (map e.succ x : E) ∈ J e ↔
          (x : P2 × ℝ).2 = t e.succ.castSucc :=
        signed_prism_end_preimage ⟨le_rfl, (ht Fin.castSucc_lt_succ).le⟩
          (map e.succ) (G e) (hlower e) x
      refine ⟨?_, ?_, ?_⟩
      · intro x
        have hs : (x : P2 × ℝ) ∈ S e.succ ↔
            (x : P2 × ℝ).2 = t e.castSucc.succ := by
          constructor
          · intro hx
            exact le_antisymm x.property.2.2 (htime ▸ hx.2.1)
          · intro hx
            refine ⟨x.property.1, ?_, ?_⟩
            · rw [hx, htime]
            · rw [hx, htime]
              exact (ht Fin.castSucc_lt_succ).le
        have hb : (map e.castSucc x : E) ∈ B e.succ ↔ (map e.castSucc x : E) ∈ J e := by
          rw [← hcontact]
          exact ⟨fun hx => ⟨(map e.castSucc x).property, hx⟩, fun hx => hx.2⟩
        exact hs.trans ((hu x).symm.trans hb.symm)
      · intro x
        have hs : (x : P2 × ℝ) ∈ S e.castSucc ↔
            (x : P2 × ℝ).2 = t e.succ.castSucc := by
          constructor
          · intro hx
            exact le_antisymm (htime ▸ hx.2.2) x.property.2.1
          · intro hx
            refine ⟨x.property.1, ?_, ?_⟩
            · rw [hx, ← htime]
              exact (ht Fin.castSucc_lt_succ).le
            · rw [hx, htime]
        have hb : (map e.succ x : E) ∈ B e.castSucc ↔ (map e.succ x : E) ∈ J e := by
          rw [← hcontact]
          exact ⟨fun hx => ⟨hx, (map e.succ x).property⟩, fun hx => hx.1⟩
        exact hs.trans ((hl x).symm.trans hb.symm)
      · intro x hi hj
        have hx : x.2 = t e.castSucc.succ := le_antisymm hi.2.2 (htime ▸ hj.2.1)
        let y : signedTubeDiamond := ⟨x.1, hi.1⟩
        have hleft : (⟨x, hi⟩ : S e.castSucc) =
            ⟨(y, t e.castSucc.succ), y.property, (ht Fin.castSucc_lt_succ).le, le_rfl⟩ :=
          Subtype.ext (Prod.ext rfl hx)
        have hright : (⟨x, hj⟩ : S e.succ) =
            ⟨(y, t e.succ.castSucc), y.property, le_rfl, (ht Fin.castSucc_lt_succ).le⟩ :=
          Subtype.ext (Prod.ext rfl (hx.trans (congrArg t htime)))
        rw [hleft, hright, hupper, hlower]
    · have hgap : i.val + 1 < j.val := by omega
      have htime : t i.succ < t j.castSucc := ht (by change i.val + 1 < j.val; exact hgap)
      have hmiss (x : P2 × ℝ) (hi : x ∈ S i) (hj : x ∈ S j) : False :=
        (not_lt_of_ge (hi.2.2.trans' hj.2.1)) htime
      have hBmiss := Set.disjoint_left.mp (hfar i j hgap)
      exact ⟨fun x => iff_of_false (hmiss x x.property) (hBmiss (map i x).property),
        fun x => iff_of_false (fun hx => hmiss x hx x.property)
          (fun hx => hBmiss hx (map j x).property),
        fun x hi hj => (hmiss x hi hj).elim⟩
  have hoverlap (i j) (x : S i) : (x : P2 × ℝ) ∈ S j ↔ (map i x : E) ∈ B j := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hordered i j hij).1 x
    · exact iff_of_true x.property (map i x).property
    · exact (hordered j i hji).2.1 x
  have hagree (i j) (x : P2 × ℝ) (hi : x ∈ S i) (hj : x ∈ S j) :
      (map i ⟨x, hi⟩ : E) = map j ⟨x, hj⟩ := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (hordered i j hij).2.2 x hi hj
    · rfl
    · exact ((hordered j i hji).2.2 x hj hi).symm
  obtain ⟨H, hH, hkeep⟩ := Homeomorph.exists_iUnion_finitePL S B map hmap hoverlap hagree
  have hSource : (⋃ i, S i) = signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨hi.1, (ht.monotone (Fin.zero_le _)).trans hi.2.1,
        hi.2.2.trans (ht.monotone (Fin.le_last _))⟩
    · intro hx
      obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hx.2
      exact mem_iUnion.mpr ⟨i, hx.1, hi⟩
  refine ⟨(Homeomorph.setCongr hSource.symm).trans H, hH.setCongr hSource rfl, ?_⟩
  exact hkeep

theorem exists_signed_prism_chain_map_of_incident_frames
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (B : Fin (n + 2) → Set E) (J : Fin (n + 1) → Set E)
    (G : ∀ e, signedTubeDiamond ≃ₜ J e)
    (hG : ∀ e, (G e).IsFinitePL)
    (left right : Fin (n + 1) → Fin 2 → Bool)
    (initial : Fin 2 → Bool)
    (map : ∀ i, ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (hcontact : ∀ e : Fin (n + 1), B e.castSucc ∩ B e.succ = J e)
    (hfar : ∀ i j, i.val + 1 < j.val → Disjoint (B i) (B j))
    (hupper : ∀ (e : Fin (n + 1)) (x : signedTubeDiamond),
      (map e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) =
          G e (signedTubeDiamondReflection (left e) x))
    (hlower : ∀ (e : Fin (n + 1)) (x : signedTubeDiamond),
      (map e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) =
          G e (signedTubeDiamondReflection (right e) x)) :
    ∃ (frame : Fin (n + 2) → Fin 2 → Bool)
      (H : ↥(signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) ≃ₜ (⋃ i, B i)),
      frame 0 = initial ∧ H.IsFinitePL ∧
      ∀ i (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ))),
        (H ⟨x, x.property.1,
          (ht.monotone (Fin.zero_le _)).trans x.property.2.1,
          x.property.2.2.trans (ht.monotone (Fin.le_last _))⟩ : E) =
          map i (signedTubePrismReparametrization
            (signedTubeDiamondReflection (frame i)) (t i.castSucc) (t i.succ) x) := by
  classical
  obtain ⟨frame, hframe0, hframe⟩ := exists_signed_path_frames n left right initial
  let maps := fun i => (signedTubePrismReparametrization
    (signedTubeDiamondReflection (frame i)) (t i.castSucc) (t i.succ)).trans (map i)
  have hmaps (i) : (maps i).IsFinitePL :=
    (signedTubePrismReparametrization_isFinitePL
      (signedTubeDiamondReflection_isFinitePL (hG 0) (frame i)) (ht Fin.castSucc_lt_succ)).trans
        (hmap i)
  let joint := fun e => ((signedTubeDiamondReflection (frame e.castSucc)).trans
    (signedTubeDiamondReflection (left e))).trans (G e)
  have hu (e) (x : signedTubeDiamond) :
      (maps e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = joint e x := by
    exact hupper e (signedTubeDiamondReflection (frame e.castSucc) x)
  have hl (e) (x : signedTubeDiamond) :
      (maps e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = joint e x := by
    exact (hlower e (signedTubeDiamondReflection (frame e.succ) x)).trans
      (congrArg Subtype.val (signedTubeDiamondReflection_incident_agreement
        (G e) (left e) (right e) (frame e.castSucc) (frame e.succ) (hframe e) x)).symm
  obtain ⟨H, hH, hkeep⟩ := exists_signed_prism_chain_map t ht B J joint maps hmaps
    hcontact hfar hu hl
  exact ⟨frame, H, hframe0, hH, hkeep⟩

end PoincareConjecture.M76.Dehn
