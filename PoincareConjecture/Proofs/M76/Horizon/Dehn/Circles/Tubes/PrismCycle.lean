import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismPreimages
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PrismEndFibers
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPaths










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)



theorem exists_signed_prism_cut_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (B : Fin (n + 2) → Set E) (J : Fin (n + 1) → Set E)
    (G : ∀ e, signedTubeDiamond ≃ₜ J e)
    (map : ∀ i, ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (hupper : ∀ (e : Fin (n + 1)) (x : signedTubeDiamond),
      (map e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = G e x)
    (hlower : ∀ (e : Fin (n + 1)) (x : signedTubeDiamond),
      (map e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = G e x) :
    ∃ τ : P2 × ℝ → E,
      FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) ∧
      (∀ i (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ))), τ x = map i x) ∧
      τ '' (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) = ⋃ i, B i := by
  classical
  let S := fun i : Fin (n + 2) ↦ signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)
  have hagree (i j : Fin (n + 2)) (x : P2 × ℝ) (hi : x ∈ S i) (hj : x ∈ S j) :
      (map i ⟨x, hi⟩ : E) = map j ⟨x, hj⟩ := by
    suffices hordered : ∀ i j : Fin (n + 2), i < j → ∀ x : P2 × ℝ,
        ∀ hi : x ∈ S i, ∀ hj : x ∈ S j, (map i ⟨x, hi⟩ : E) = map j ⟨x, hj⟩ by
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact hordered i j hij x hi hj
      · rfl
      · exact (hordered j i hji x hj hi).symm
    intro i j hij x hi hj
    have hnext : i.val + 1 = j.val := by
      by_contra hne
      have hlt : t i.succ < t j.castSucc := ht (by change i.val + 1 < j.val; omega)
      exact (not_lt_of_ge (hi.2.2.trans' hj.2.1)) hlt
    obtain ⟨e, hei, hej⟩ : ∃ e : Fin (n + 1), e.castSucc = i ∧ e.succ = j := by
      exact ⟨⟨i.val, by have hj := j.isLt; omega⟩, Fin.ext rfl, Fin.ext hnext⟩
    subst i
    subst j
    have htime : e.castSucc.succ = e.succ.castSucc := Fin.ext rfl
    have hx : x.2 = t e.castSucc.succ := le_antisymm hi.2.2 (htime ▸ hj.2.1)
    let y : signedTubeDiamond := ⟨x.1, hi.1⟩
    have hleft : (⟨x, hi⟩ : S e.castSucc) =
        ⟨(y, t e.castSucc.succ), y.property, (ht Fin.castSucc_lt_succ).le, le_rfl⟩ :=
      Subtype.ext (Prod.ext rfl hx)
    have hright : (⟨x, hj⟩ : S e.succ) =
        ⟨(y, t e.succ.castSucc), y.property, le_rfl, (ht Fin.castSucc_lt_succ).le⟩ :=
      Subtype.ext (Prod.ext rfl (hx.trans (congrArg t htime)))
    rw [hleft, hright, hupper, hlower]
  let τ : P2 × ℝ → E := fun x ↦ if hx : x ∈ ⋃ i, S i then
    map (mem_iUnion.mp hx).choose ⟨x, (mem_iUnion.mp hx).choose_spec⟩ else 0
  have hval (i : Fin (n + 2)) (x : S i) : τ x = map i x := by
    have hx : (x : P2 × ℝ) ∈ ⋃ i, S i := mem_iUnion.mpr ⟨i, x.property⟩
    dsimp only [τ]
    rw [dif_pos hx]
    exact hagree _ i x _ x.property
  have hPL (i : Fin (n + 2)) : FinitePiecewiseAffineOn τ (S i) := by
    obtain ⟨g, hg, hgval⟩ := hmap i
    exact hg.congr (fun x hx ↦ (hgval ⟨x, hx⟩).symm.trans (hval i ⟨x, hx⟩).symm)
  have hsource : (⋃ i, S i) = signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 2))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨hi.1, (ht.monotone (Fin.zero_le _)).trans hi.2.1,
        hi.2.2.trans (ht.monotone (Fin.le_last _))⟩
    · intro hx
      obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hx.2
      exact mem_iUnion.mpr ⟨i, hx.1, hi⟩
  refine ⟨τ, hsource ▸ FinitePiecewiseAffineOn.iUnion hPL, hval, ?_⟩
  rw [← hsource]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hval i ⟨x, hi⟩]
    exact mem_iUnion.mpr ⟨i, (map i ⟨x, hi⟩).property⟩
  · intro hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    let x := (map i).symm ⟨y, hi⟩
    exact ⟨x, mem_iUnion.mpr ⟨i, x.property⟩,
      (hval i x).trans (congrArg Subtype.val ((map i).apply_symm_apply ⟨y, hi⟩))⟩



theorem exists_signed_prism_cycle_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (t : Fin (n + 4) → ℝ) (ht : StrictMono t)
    (B : Fin (n + 3) → Set E) (J : Fin (n + 2) → Set E)
    (G : ∀ e, signedTubeDiamond ≃ₜ J e)
    (map : ∀ i, ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (hcontact : ∀ e : Fin (n + 2), B e.castSucc ∩ B e.succ = J e)
    (hupper : ∀ (e : Fin (n + 2)) (x : signedTubeDiamond),
      (map e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = G e x)
    (hlower : ∀ (e : Fin (n + 2)) (x : signedTubeDiamond),
      (map e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = G e x)
    (Jclose : Set E) (Gclose : signedTubeDiamond ≃ₜ Jclose)
    (closing : signedTubeDiamond ≃ₜ signedTubeDiamond)
    (hclose : B 0 ∩ B (Fin.last (n + 2)) = Jclose)
    (hfirst : ∀ x : signedTubeDiamond,
      (map 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by change (0 : ℕ) < 1; omega)).le⟩ : E) =
          Gclose (closing x))
    (hlast : ∀ x : signedTubeDiamond,
      (map (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = Gclose x)
    (hfar : ∀ i j : Fin (n + 3), i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = Fin.last (n + 2)) → Disjoint (B i) (B j)) :
    ∃ τ : P2 × ℝ → E,
      FinitePiecewiseAffineOn τ (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 3)))) ∧
      (∀ i (x : ↥(signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ))), τ x = map i x) ∧
      τ '' (signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 3)))) = ⋃ i, B i ∧
      ∀ x y : ↥(signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 3)))),
        τ x = τ y ↔ x = y ∨
          ((x : P2 × ℝ).2 = t 0 ∧ (y : P2 × ℝ).2 = t (Fin.last (n + 3)) ∧
            (closing ⟨(x : P2 × ℝ).1, x.property.1⟩ : P2) = (y : P2 × ℝ).1) ∨
          ((y : P2 × ℝ).2 = t 0 ∧ (x : P2 × ℝ).2 = t (Fin.last (n + 3)) ∧
            (closing ⟨(y : P2 × ℝ).1, y.property.1⟩ : P2) = (x : P2 × ℝ).1) := by
  obtain ⟨τ, hτ, hval, himage⟩ := exists_signed_prism_cut_map t ht B J G map hmap hupper hlower
  let S := fun i : Fin (n + 3) ↦ signedTubeDiamond ×ˢ Icc (t i.castSucc) (t i.succ)
  have hordered (i j : Fin (n + 3)) (hij : i < j) (x : S i) (y : S j)
      (hxy : (map i x : E) = map j y) :
      (x : P2 × ℝ) = y ∨
        ((x : P2 × ℝ).2 = t 0 ∧ (y : P2 × ℝ).2 = t (Fin.last (n + 3)) ∧
          (closing ⟨(x : P2 × ℝ).1, x.property.1⟩ : P2) = (y : P2 × ℝ).1) := by
    by_cases hnext : i.val + 1 = j.val
    · obtain ⟨e, hei, hej⟩ : ∃ e : Fin (n + 2), e.castSucc = i ∧ e.succ = j := by
        exact ⟨⟨i.val, by have hj := j.isLt; omega⟩, Fin.ext rfl, Fin.ext hnext⟩
      subst i
      subst j
      have htime : e.castSucc.succ = e.succ.castSucc := Fin.ext rfl
      have h := (signed_prism_joint_fiber_iff
        ⟨t e.castSucc.succ, (ht Fin.castSucc_lt_succ).le, le_rfl⟩
        ⟨t e.succ.castSucc, le_rfl, (ht Fin.castSucc_lt_succ).le⟩
        (map e.castSucc) (map e.succ) (G e) (Homeomorph.refl _)
        (hcontact e) (hupper e) (hlower e) x y).mp hxy
      exact Or.inl (Prod.ext h.2.2 (h.1.trans ((congrArg t htime).trans h.2.1.symm)))
    · by_cases hwrap : i = 0 ∧ j = Fin.last (n + 2)
      · obtain ⟨rfl, rfl⟩ := hwrap
        exact Or.inr ((signed_prism_joint_fiber_iff
          ⟨t 0, le_rfl, (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by change (0 : ℕ) < 1; omega)).le⟩
          ⟨t (Fin.last (n + 3)), (ht Fin.castSucc_lt_succ).le, le_rfl⟩
          (map 0) (map (Fin.last (n + 2))) Gclose closing hclose hfirst hlast x y).mp hxy)
      · have hgap : i.val + 1 < j.val := by omega
        exact (disjoint_left.mp (hfar i j hgap hwrap) (map i x).property
          (hxy.symm ▸ (map j y).property)).elim
  have hτfirst (x : signedTubeDiamond) : τ (x, t 0) = Gclose (closing x) :=
    (hval 0 ⟨(x, t 0), x.property, le_rfl,
      (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ from by change (0 : ℕ) < 1; omega)).le⟩).trans (hfirst x)
  have hτlast (x : signedTubeDiamond) : τ (x, t (Fin.last (n + 3))) = Gclose x :=
    (hval (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
      (ht Fin.castSucc_lt_succ).le, le_rfl⟩).trans (hlast x)
  have hclosing (x y : ↥(signedTubeDiamond ×ˢ Icc (t 0) (t (Fin.last (n + 3)))))
      (hx : (x : P2 × ℝ).2 = t 0) (hy : (y : P2 × ℝ).2 = t (Fin.last (n + 3)))
      (hcoord : (closing ⟨(x : P2 × ℝ).1, x.property.1⟩ : P2) = (y : P2 × ℝ).1) :
      τ x = τ y := by
    have hleft := hτfirst ⟨(x : P2 × ℝ).1, x.property.1⟩
    have hright := hτlast ⟨(y : P2 × ℝ).1, y.property.1⟩
    have hxform : (x : P2 × ℝ) = ((x : P2 × ℝ).1, t 0) := Prod.ext rfl hx
    have hyform : (y : P2 × ℝ) = ((y : P2 × ℝ).1, t (Fin.last (n + 3))) := Prod.ext rfl hy
    rw [← hxform] at hleft
    rw [← hyform] at hright
    exact hleft.trans ((congrArg (fun z : signedTubeDiamond ↦ (Gclose z : E))
      (Subtype.ext hcoord)).trans hright.symm)
  refine ⟨τ, hτ, hval, himage, ?_⟩
  intro x y
  constructor
  · intro hxy
    obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc x.property.2
    obtain ⟨j, hj⟩ := ht.monotone.exists_mem_consecutive_Icc y.property.2
    let xi : S i := ⟨x, x.property.1, hi⟩
    let yj : S j := ⟨y, y.property.1, hj⟩
    have heq : (map i xi : E) = map j yj :=
      (hval i xi).symm.trans (hxy.trans (hval j yj))
    rcases lt_trichotomy i j with hij | rfl | hji
    · rcases hordered i j hij xi yj heq with hsame | hwrap
      · exact Or.inl (Subtype.ext hsame)
      · exact Or.inr (Or.inl hwrap)
    · have hsame : xi = yj := (map i).injective (Subtype.ext heq)
      exact Or.inl (Subtype.ext (congrArg (fun z : S i ↦ (z : P2 × ℝ)) hsame))
    · rcases hordered j i hji yj xi heq.symm with hsame | hwrap
      · exact Or.inl (Subtype.ext hsame.symm)
      · exact Or.inr (Or.inr hwrap)
  · rintro (rfl | ⟨hx, hy, hcoord⟩ | ⟨hy, hx, hcoord⟩)
    · rfl
    · exact hclosing x y hx hy hcoord
    · exact (hclosing y x hy hx hcoord).symm

end PoincareConjecture.M76.Dehn
