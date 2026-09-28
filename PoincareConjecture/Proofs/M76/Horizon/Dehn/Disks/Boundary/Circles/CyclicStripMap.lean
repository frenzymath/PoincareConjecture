import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismPreimages
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPaths









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn


private theorem product_joint_fiber_iff
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] {S : Set F} {B C J : Set E}
    {α β γ δ : ℝ} (u : Icc α β) (v : Icc γ δ)
    (left : ↥(S ×ˢ Icc α β) ≃ₜ B) (right : ↥(S ×ˢ Icc γ δ) ≃ₜ C)
    (G : S ≃ₜ J) (closing : S ≃ₜ S) (hcontact : B ∩ C = J)
    (hl : ∀ x : S, (left ⟨(x, u), x.property, u.property⟩ : E) = G (closing x))
    (hr : ∀ x : S, (right ⟨(x, v), x.property, v.property⟩ : E) = G x)
    (x : ↥(S ×ˢ Icc α β)) (y : ↥(S ×ˢ Icc γ δ)) :
    (left x : E) = right y ↔
      (x : F × ℝ).2 = u ∧ (y : F × ℝ).2 = v ∧
      (closing ⟨(x : F × ℝ).1, x.property.1⟩ : F) = (y : F × ℝ).1 := by
  constructor
  · intro hxy
    let z : J := ⟨left x, hcontact ▸ ⟨(left x).property, hxy.symm ▸ (right y).property⟩⟩
    let a := closing.symm (G.symm z)
    let b := G.symm z
    have hx : x = ⟨(a, u), a.property, u.property⟩ := by
      apply left.injective
      apply Subtype.ext
      rw [hl]
      exact (congrArg Subtype.val (by simp only [a, closing.apply_symm_apply,
        G.apply_symm_apply] : G (closing a) = z)).symm
    have hy : y = ⟨(b, v), b.property, v.property⟩ := by
      apply right.injective
      apply Subtype.ext
      rw [hr]
      exact hxy.symm.trans (congrArg Subtype.val (G.apply_symm_apply z)).symm
    rw [hx, hy]
    exact ⟨rfl, rfl, congrArg Subtype.val (closing.apply_symm_apply b)⟩
  · rintro ⟨hx, hy, hcoord⟩
    have hxform : x = ⟨((x : F × ℝ).1, u), x.property.1, u.property⟩ :=
      Subtype.ext (Prod.ext rfl hx)
    have hyform : y = ⟨((y : F × ℝ).1, v), y.property.1, v.property⟩ :=
      Subtype.ext (Prod.ext rfl hy)
    have hleft := hl ⟨(x : F × ℝ).1, x.property.1⟩
    have hright := hr ⟨(y : F × ℝ).1, y.property.1⟩
    rw [← hxform] at hleft
    rw [← hyform] at hright
    exact hleft.trans ((congrArg (fun z : S ↦ (G z : E))
      (Subtype.ext hcoord)).trans hright.symm)



private theorem exists_product_cut_map
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (S : Set F)
    {n : ℕ} (t : Fin (n + 3) → ℝ) (ht : StrictMono t)
    (B : Fin (n + 2) → Set E) (J : Fin (n + 1) → Set E)
    (G : ∀ e, S ≃ₜ J e)
    (map : ∀ i, ↥(S ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (hupper : ∀ (e : Fin (n + 1)) (x : S),
      (map e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = G e x)
    (hlower : ∀ (e : Fin (n + 1)) (x : S),
      (map e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = G e x) :
    ∃ τ : F × ℝ → E,
      FinitePiecewiseAffineOn τ (S ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) ∧
      (∀ i (x : ↥(S ×ˢ Icc (t i.castSucc) (t i.succ))), τ x = map i x) ∧
      τ '' (S ×ˢ Icc (t 0) (t (Fin.last (n + 2)))) = ⋃ i, B i := by
  classical
  let block := fun i : Fin (n + 2) ↦ S ×ˢ Icc (t i.castSucc) (t i.succ)
  have hagree (i j : Fin (n + 2)) (x : F × ℝ) (hi : x ∈ block i) (hj : x ∈ block j) :
      (map i ⟨x, hi⟩ : E) = map j ⟨x, hj⟩ := by
    suffices hordered : ∀ i j : Fin (n + 2), i < j → ∀ x : F × ℝ,
        ∀ hi : x ∈ block i, ∀ hj : x ∈ block j, (map i ⟨x, hi⟩ : E) = map j ⟨x, hj⟩ by
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
    let y : S := ⟨x.1, hi.1⟩
    have hleft : (⟨x, hi⟩ : block e.castSucc) =
        ⟨(y, t e.castSucc.succ), y.property, (ht Fin.castSucc_lt_succ).le, le_rfl⟩ :=
      Subtype.ext (Prod.ext rfl hx)
    have hright : (⟨x, hj⟩ : block e.succ) =
        ⟨(y, t e.succ.castSucc), y.property, le_rfl, (ht Fin.castSucc_lt_succ).le⟩ :=
      Subtype.ext (Prod.ext rfl (hx.trans (congrArg t htime)))
    rw [hleft, hright, hupper, hlower]
  let τ : F × ℝ → E := fun x ↦ if hx : x ∈ ⋃ i, block i then
    map (mem_iUnion.mp hx).choose ⟨x, (mem_iUnion.mp hx).choose_spec⟩ else 0
  have hval (i : Fin (n + 2)) (x : block i) : τ x = map i x := by
    have hx : (x : F × ℝ) ∈ ⋃ i, block i := mem_iUnion.mpr ⟨i, x.property⟩
    dsimp only [τ]
    rw [dif_pos hx]
    exact hagree _ i x _ x.property
  have hPL (i : Fin (n + 2)) : FinitePiecewiseAffineOn τ (block i) := by
    obtain ⟨g, hg, hgval⟩ := hmap i
    exact hg.congr (fun x hx ↦ (hgval ⟨x, hx⟩).symm.trans (hval i ⟨x, hx⟩).symm)
  have hsource : (⋃ i, block i) = S ×ˢ Icc (t 0) (t (Fin.last (n + 2))) := by
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



private theorem exists_product_cycle_map
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (S : Set F)
    {n : ℕ} (t : Fin (n + 4) → ℝ) (ht : StrictMono t)
    (B : Fin (n + 3) → Set E) (J : Fin (n + 2) → Set E)
    (G : ∀ e, S ≃ₜ J e)
    (map : ∀ i, ↥(S ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (hcontact : ∀ e : Fin (n + 2), B e.castSucc ∩ B e.succ = J e)
    (hupper : ∀ (e : Fin (n + 2)) (x : S),
      (map e.castSucc ⟨(x, t e.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = G e x)
    (hlower : ∀ (e : Fin (n + 2)) (x : S),
      (map e.succ ⟨(x, t e.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = G e x)
    (Jclose : Set E) (Gclose : S ≃ₜ Jclose)
    (closing : S ≃ₜ S)
    (hclose : B 0 ∩ B (Fin.last (n + 2)) = Jclose)
    (hfirst : ∀ x : S,
      (map 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ by
          change (0 : ℕ) < 1; omega)).le⟩ : E) =
          Gclose (closing x))
    (hlast : ∀ x : S,
      (map (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = Gclose x)
    (hfar : ∀ i j : Fin (n + 3), i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = Fin.last (n + 2)) → Disjoint (B i) (B j)) :
    ∃ τ : F × ℝ → E,
      FinitePiecewiseAffineOn τ (S ×ˢ Icc (t 0) (t (Fin.last (n + 3)))) ∧
      (∀ i (x : ↥(S ×ˢ Icc (t i.castSucc) (t i.succ))), τ x = map i x) ∧
      τ '' (S ×ˢ Icc (t 0) (t (Fin.last (n + 3)))) = ⋃ i, B i ∧
      ∀ x y : ↥(S ×ˢ Icc (t 0) (t (Fin.last (n + 3)))),
        τ x = τ y ↔ x = y ∨
          ((x : F × ℝ).2 = t 0 ∧ (y : F × ℝ).2 = t (Fin.last (n + 3)) ∧
            (closing ⟨(x : F × ℝ).1, x.property.1⟩ : F) = (y : F × ℝ).1) ∨
          ((y : F × ℝ).2 = t 0 ∧ (x : F × ℝ).2 = t (Fin.last (n + 3)) ∧
            (closing ⟨(y : F × ℝ).1, y.property.1⟩ : F) = (x : F × ℝ).1) := by
  obtain ⟨τ, hτ, hval, himage⟩ := exists_product_cut_map S t ht B J G map hmap hupper hlower
  let block := fun i : Fin (n + 3) ↦ S ×ˢ Icc (t i.castSucc) (t i.succ)
  have hordered (i j : Fin (n + 3)) (hij : i < j) (x : block i) (y : block j)
      (hxy : (map i x : E) = map j y) :
      (x : F × ℝ) = y ∨
        ((x : F × ℝ).2 = t 0 ∧ (y : F × ℝ).2 = t (Fin.last (n + 3)) ∧
          (closing ⟨(x : F × ℝ).1, x.property.1⟩ : F) = (y : F × ℝ).1) := by
    by_cases hnext : i.val + 1 = j.val
    · obtain ⟨e, hei, hej⟩ : ∃ e : Fin (n + 2), e.castSucc = i ∧ e.succ = j := by
        exact ⟨⟨i.val, by have hj := j.isLt; omega⟩, Fin.ext rfl, Fin.ext hnext⟩
      subst i
      subst j
      have htime : e.castSucc.succ = e.succ.castSucc := Fin.ext rfl
      have h := (product_joint_fiber_iff
        ⟨t e.castSucc.succ, (ht Fin.castSucc_lt_succ).le, le_rfl⟩
        ⟨t e.succ.castSucc, le_rfl, (ht Fin.castSucc_lt_succ).le⟩
        (map e.castSucc) (map e.succ) (G e) (Homeomorph.refl _)
        (hcontact e) (hupper e) (hlower e) x y).mp hxy
      exact Or.inl (Prod.ext h.2.2 (h.1.trans ((congrArg t htime).trans h.2.1.symm)))
    · by_cases hwrap : i = 0 ∧ j = Fin.last (n + 2)
      · obtain ⟨rfl, rfl⟩ := hwrap
        exact Or.inr ((product_joint_fiber_iff
          ⟨t 0, le_rfl, (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ by
            change (0 : ℕ) < 1; omega)).le⟩
          ⟨t (Fin.last (n + 3)), (ht Fin.castSucc_lt_succ).le, le_rfl⟩
          (map 0) (map (Fin.last (n + 2))) Gclose closing hclose hfirst hlast x y).mp hxy)
      · have hgap : i.val + 1 < j.val := by omega
        exact (disjoint_left.mp (hfar i j hgap hwrap) (map i x).property
          (hxy.symm ▸ (map j y).property)).elim
  have hτfirst (x : S) : τ (x, t 0) = Gclose (closing x) :=
    (hval 0 ⟨(x, t 0), x.property, le_rfl,
      (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ by
        change (0 : ℕ) < 1; omega)).le⟩).trans (hfirst x)
  have hτlast (x : S) : τ (x, t (Fin.last (n + 3))) = Gclose x :=
    (hval (Fin.last (n + 2)) ⟨(x, t (Fin.last (n + 3))), x.property,
      (ht Fin.castSucc_lt_succ).le, le_rfl⟩).trans (hlast x)
  have hclosing (x y : ↥(S ×ˢ Icc (t 0) (t (Fin.last (n + 3)))))
      (hx : (x : F × ℝ).2 = t 0) (hy : (y : F × ℝ).2 = t (Fin.last (n + 3)))
      (hcoord : (closing ⟨(x : F × ℝ).1, x.property.1⟩ : F) = (y : F × ℝ).1) :
      τ x = τ y := by
    have hleft := hτfirst ⟨(x : F × ℝ).1, x.property.1⟩
    have hright := hτlast ⟨(y : F × ℝ).1, y.property.1⟩
    have hxform : (x : F × ℝ) = ((x : F × ℝ).1, t 0) := Prod.ext rfl hx
    have hyform : (y : F × ℝ) = ((y : F × ℝ).1, t (Fin.last (n + 3))) := Prod.ext rfl hy
    rw [← hxform] at hleft
    rw [← hyform] at hright
    exact hleft.trans ((congrArg (fun z : S ↦ (Gclose z : E))
      (Subtype.ext hcoord)).trans hright.symm)
  refine ⟨τ, hτ, hval, himage, ?_⟩
  intro x y
  constructor
  · intro hxy
    obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc x.property.2
    obtain ⟨j, hj⟩ := ht.monotone.exists_mem_consecutive_Icc y.property.2
    let xi : block i := ⟨x, x.property.1, hi⟩
    let yj : block j := ⟨y, y.property.1, hj⟩
    have heq : (map i xi : E) = map j yj :=
      (hval i xi).symm.trans (hxy.trans (hval j yj))
    rcases lt_trichotomy i j with hij | rfl | hji
    · rcases hordered i j hij xi yj heq with hsame | hwrap
      · exact Or.inl (Subtype.ext hsame)
      · exact Or.inr (Or.inl hwrap)
    · have hsame : xi = yj := (map i).injective (Subtype.ext heq)
      exact Or.inl (Subtype.ext (congrArg (fun z : block i ↦ (z : F × ℝ)) hsame))
    · rcases hordered j i hji yj xi heq.symm with hsame | hwrap
      · exact Or.inl (Subtype.ext hsame.symm)
      · exact Or.inr (Or.inr hwrap)
  · rintro (rfl | ⟨hx, hy, hcoord⟩ | ⟨hy, hx, hcoord⟩)
    · rfl
    · exact hclosing x y hx hy hcoord
    · exact (hclosing y x hy hx hcoord).symm

local notation "P2" => (ℝ × ℝ)

private theorem exists_translated_unit_strip_block
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (map : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ B)
    (hmap : map.IsFinitePL) (a : ℝ) :
    ∃ shifted : ↥(signedTubeSheet 0 ×ˢ Icc a (a + 1)) ≃ₜ B,
      shifted.IsFinitePL ∧ ∀ x,
        (shifted x : E) = map ⟨((x : P2 × ℝ).1, (x : P2 × ℝ).2 - a),
          x.property.1, by constructor <;> linarith [x.property.2.1, x.property.2.2]⟩ := by
  let shift : (P2 × ℝ) →ᴬ[ℝ] (P2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.prod
      ((ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap +
        ContinuousAffineMap.const ℝ (P2 × ℝ) a)
  have hval (x : P2 × ℝ) : shift x = (x.1, x.2 + a) := rfl
  have hinj : Function.Injective shift := by
    intro x y h
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    exact Prod.ext h0 (add_right_cancel h1)
  have himage : shift '' (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) =
      signedTubeSheet 0 ×ˢ Icc a (a + 1) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, by change a ≤ y.2 + a; linarith [hy.2.1],
        by change y.2 + a ≤ a + 1; linarith [hy.2.2]⟩
    · intro hx
      refine ⟨(x.1, x.2 - a), ⟨hx.1, ?_, ?_⟩, ?_⟩
      · linarith [hx.2.1]
      · linarith [hx.2.2]
      · simp [hval]
  have hmap' := hmap
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hmap'
  have hshift : FinitePiecewiseAffineOn shift (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine shift⟩
  have he := hshift.exists_homeomorph_image hinj.injOn
  rw [himage] at he
  obtain ⟨e, he, heval⟩ := he
  refine ⟨e.symm.trans map, he.symm.trans hmap, ?_⟩
  intro x
  apply congrArg (fun z ↦ (map z : E))
  apply Subtype.ext
  have hv := heval (e.symm x)
  rw [e.apply_symm_apply] at hv
  have hv0 := congrArg Prod.fst hv
  have hv1 := congrArg Prod.snd hv
  refine Prod.ext hv0.symm ?_
  change (e.symm x : P2 × ℝ).2 = x.val.2 - a
  change x.val.2 = (e.symm x : P2 × ℝ).2 + a at hv1
  linarith



theorem exists_cyclic_strip_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (B J : Fin (n + 3) → Set E) (G : ∀ i, signedTubeSheet 0 ≃ₜ J i)
    (map : ∀ i, ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ B i)
    (hmap : ∀ i, (map i).IsFinitePL)
    (hlower : ∀ i (x : signedTubeSheet 0),
      (map i ⟨(x, 0), x.property, le_rfl, zero_le_one⟩ : E) =
        G ((finRotate (n + 3)).symm i) x)
    (hupper : ∀ i (x : signedTubeSheet 0),
      (map i ⟨(x, 1), x.property, zero_le_one, le_rfl⟩ : E) = G i x)
    (hcontact : ∀ i : Fin (n + 2), B i.castSucc ∩ B i.succ = J i.castSucc)
    (hclose : B 0 ∩ B (Fin.last (n + 2)) = J (Fin.last (n + 2)))
    (hfar : ∀ i j : Fin (n + 3), i.val + 1 < j.val →
      ¬ (i = 0 ∧ j = Fin.last (n + 2)) → Disjoint (B i) (B j)) :
    ∃ sigma : P2 × ℝ → E,
      FinitePiecewiseAffineOn sigma (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)) ∧
      sigma '' (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)) = ⋃ i, B i ∧
      (∀ i (x : ↥(signedTubeSheet 0 ×ˢ Icc (i.val : ℝ) (i.val + 1))),
        sigma x = map i ⟨((x : P2 × ℝ).1, (x : P2 × ℝ).2 - i.val), x.property.1,
          by constructor <;> linarith [x.property.2.1, x.property.2.2]⟩) ∧
      ∀ x y : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)),
        sigma x = sigma y ↔ x = y ∨
          ((x : P2 × ℝ).2 = 0 ∧ (y : P2 × ℝ).2 = n + 3 ∧
            (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
          ((y : P2 × ℝ).2 = 0 ∧ (x : P2 × ℝ).2 = n + 3 ∧
            (y : P2 × ℝ).1 = (x : P2 × ℝ).1) := by
  classical
  let t : Fin (n + 4) → ℝ := fun i ↦ i.val
  have ht : StrictMono t := fun _ _ h ↦ Nat.cast_lt.mpr h
  have hprev (i : Fin (n + 2)) : (finRotate (n + 3)).symm i.succ = i.castSucc := by
    apply (Equiv.symm_apply_eq _).mpr
    apply Fin.ext
    rw [coe_finRotate_of_ne_last]
    · rfl
    · intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at hh
      omega
  have hfirst : (finRotate (n + 3)).symm 0 = Fin.last (n + 2) :=
    (Equiv.symm_apply_eq _).mpr finRotate_last.symm
  have hshift (i : Fin (n + 3)) :
      ∃ shifted : ↥(signedTubeSheet 0 ×ˢ Icc (t i.castSucc) (t i.succ)) ≃ₜ B i,
        shifted.IsFinitePL ∧ ∀ x,
          (shifted x : E) = map i
            ⟨((x : P2 × ℝ).1, (x : P2 × ℝ).2 - (i.val : ℝ)), x.property.1,
              by
                have h0 := x.property.2.1
                have h1 := x.property.2.2
                simp only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h0 h1
                constructor <;> linarith⟩ := by
    obtain ⟨shifted, hPL, hvalue⟩ := exists_translated_unit_strip_block (map i) (hmap i) i.val
    have hs : signedTubeSheet 0 ×ˢ Icc (i.val : ℝ) (i.val + 1) =
        signedTubeSheet 0 ×ˢ Icc (t i.castSucc) (t i.succ) := by simp [t]
    refine ⟨(Homeomorph.setCongr hs.symm).trans
      (shifted.trans (Homeomorph.setCongr rfl)), hPL.setCongr hs rfl, ?_⟩
    intro x
    exact hvalue ⟨x, hs.symm ▸ x.property⟩
  choose shifted hshiftPL hshiftValue using hshift
  have hu (i : Fin (n + 2)) (x : signedTubeSheet 0) :
      (shifted i.castSucc ⟨(x, t i.castSucc.succ), x.property,
        (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = G i.castSucc x := by
    rw [hshiftValue]
    convert hupper i.castSucc x using 1
    norm_num [t, Nat.cast_add]
  have hl (i : Fin (n + 2)) (x : signedTubeSheet 0) :
      (shifted i.succ ⟨(x, t i.succ.castSucc), x.property,
        le_rfl, (ht Fin.castSucc_lt_succ).le⟩ : E) = G i.castSucc x := by
    rw [hshiftValue]
    have h := hlower i.succ x
    rw [hprev] at h
    simpa only [t, Fin.val_castSucc, sub_self] using h
  have hf (x : signedTubeSheet 0) :
      (shifted 0 ⟨(x, t 0), x.property, le_rfl,
        (ht (show (0 : Fin (n + 4)) < (0 : Fin (n + 3)).succ by
          change (0 : ℕ) < 1; omega)).le⟩ : E) = G (Fin.last (n + 2)) x := by
    rw [hshiftValue]
    have h := hlower 0 x
    rw [hfirst] at h
    simpa only [t, Fin.val_zero, Nat.cast_zero, sub_zero] using h
  have he (x : signedTubeSheet 0) :
      (shifted (Fin.last (n + 2))
        ⟨(x, t (Fin.last (n + 3))), x.property,
          (ht Fin.castSucc_lt_succ).le, le_rfl⟩ : E) = G (Fin.last (n + 2)) x := by
    rw [hshiftValue]
    convert hupper (Fin.last (n + 2)) x using 1
    norm_num [t, Nat.cast_add]
  obtain ⟨sigma, hPL, hvalue, himage, hfib⟩ :=
    exists_product_cycle_map (signedTubeSheet 0) t ht B (fun i ↦ J i.castSucc)
      (fun i ↦ G i.castSucc) shifted hshiftPL hcontact hu hl _ (G (Fin.last (n + 2)))
      (Homeomorph.refl _) hclose hf he hfar
  refine ⟨sigma, ?_, ?_, ?_, ?_⟩
  · simpa only [t, Fin.val_zero, Nat.cast_zero, Fin.val_last, Nat.cast_add,
      Nat.cast_ofNat] using hPL
  · simpa only [t, Fin.val_zero, Nat.cast_zero, Fin.val_last, Nat.cast_add,
      Nat.cast_ofNat] using himage
  · intro i x
    have hx : (x : P2 × ℝ) ∈ signedTubeSheet 0 ×ˢ Icc (t i.castSucc) (t i.succ) := by
      simpa only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
        using x.property
    exact (hvalue i ⟨x, hx⟩).trans (hshiftValue i ⟨x, hx⟩)
  · simpa [t] using hfib



theorem cyclic_strip_axis_iff
    {E : Type*} [TopologicalSpace E] {n : ℕ}
    (B : Fin (n + 3) → Set E)
    (map : ∀ i, ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1) ≃ₜ B i)
    (sigma : P2 × ℝ → E)
    (hvalue : ∀ i (x : ↥(signedTubeSheet 0 ×ˢ Icc (i.val : ℝ) (i.val + 1))),
      sigma x = map i ⟨((x : P2 × ℝ).1, (x : P2 × ℝ).2 - i.val), x.property.1,
        by constructor <;> linarith [x.property.2.1, x.property.2.2]⟩)
    (Z : Set E)
    (haxis : ∀ i (x : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) 1)),
      (map i x : E) ∈ Z ↔ (x : P2 × ℝ).1 = (0, 0)) :
    ∀ x ∈ signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3),
      sigma x ∈ Z ↔ x.1 = (0, 0) := by
  let t : Fin (n + 4) → ℝ := fun i ↦ i.val
  have ht : StrictMono t := fun _ _ h ↦ Nat.cast_lt.mpr h
  intro x hx
  have hxt : x.2 ∈ Icc (t 0) (t (Fin.last (n + 3))) := by
    simpa only [t, Fin.val_zero, Fin.val_last, Nat.cast_zero, Nat.cast_add, Nat.cast_ofNat]
      using hx.2
  obtain ⟨i, hi⟩ := ht.monotone.exists_mem_consecutive_Icc hxt
  have hi' : x.2 ∈ Icc (i.val : ℝ) (i.val + 1) := by
    simpa only [t, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using hi
  rw [hvalue i ⟨x, hx.1, hi'⟩]
  exact haxis i _

end PoincareConjecture.M76.Dehn
