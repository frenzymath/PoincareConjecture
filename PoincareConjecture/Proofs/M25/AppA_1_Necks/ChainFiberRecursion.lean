import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Data.Int.Init
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture




theorem exists_integer_cylinder_cocycle
    {L : ℝ} (hL : 0 < L)
    (A : ℤ → Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞)
    (D : ℤ → Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞)
    (m p : ℤ → UnitTwoSphere → ℝ)
    (hfirst : ∀ i : ℤ, ∀ z : RoundCylinderSpace, (D i z).1 = A i z.1)
    (hmono : ∀ i : ℤ, ∀ q : UnitTwoSphere,
      StrictMono (fun s : ℝ => (D i (q, s)).2))
    (hshift : ∀ i : ℤ, ∀ q : UnitTwoSphere,
      m i q < -(3 * L / 16) ∧ p i q < -(9 * L / 32))
    (hlower : ∀ i : ℤ, ∀ q : UnitTwoSphere, ∀ s : ℝ,
      s ≤ 11 * L / 16 → D i (q, s) = (A i q, s + m i q))
    (hupper : ∀ i : ℤ, ∀ q : UnitTwoSphere, ∀ s : ℝ,
      13 * L / 16 ≤ s → D i (q, s) = (A i q, s + p i q))
    (k : ℤ) :
    ∃ (F : ℤ → Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞)
      (B : ℤ → Diffeomorph (𝓡 2) (𝓡 2)
        UnitTwoSphere UnitTwoSphere ∞)
      (c : ℤ → UnitTwoSphere → ℝ),
      F k = Diffeomorph.refl ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace ∞ ∧
      B k = Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞ ∧
      (∀ i : ℤ, F i = (D i).trans (F (i + 1)) ∧
        B i = (A i).trans (B (i + 1))) ∧
      (∀ i : ℤ, ∀ z : RoundCylinderSpace,
        (F i z).1 = B i z.1 ∧ ((F i).symm z).1 = (B i).symm z.1) ∧
      (∀ i : ℤ, ∀ q : UnitTwoSphere,
        StrictMono (fun s : ℝ => (F i (q, s)).2)) ∧
      (∀ i : ℤ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (c i)) ∧
      (∀ i : ℤ, k ≤ i →
        (∀ q : UnitTwoSphere, ∀ s : ℝ, 9 * L / 16 ≤ s →
          F i (q, s) = (B i q, s + c i q)) ∧
        (∀ q : UnitTwoSphere, ((i - k : ℤ) : ℝ) * (9 * L / 32) ≤ c i q)) ∧
      (∀ i : ℤ, i ≤ k →
        (∀ q : UnitTwoSphere, ∀ s : ℝ, s ≤ 5 * L / 8 →
          F i (q, s) = (B i q, s + c i q)) ∧
        (∀ q : UnitTwoSphere, c i q ≤ -(((k - i : ℤ) : ℝ) * (3 * L / 16)))) := by
  classical
  let J := (𝓡 2).prod 𝓘(ℝ, ℝ)
  let X : ℤ →
      Diffeomorph J J RoundCylinderSpace RoundCylinderSpace ∞ ×
        Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ := fun i =>
    Int.inductionOn' i k
      (Diffeomorph.refl J RoundCylinderSpace ∞,
        Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞)
      (fun j _ e => ((D j).symm.trans e.1, (A j).symm.trans e.2))
      (fun j _ e => ((D (j - 1)).trans e.1, (A (j - 1)).trans e.2))
  let F := fun i => (X i).1
  let B := fun i => (X i).2
  have hXbase : X k = (Diffeomorph.refl J RoundCylinderSpace ∞,
      Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞) := by
    exact Int.inductionOn'_self
  have hXsucc (i : ℤ) (hi : k ≤ i) :
      X (i + 1) = ((D i).symm.trans (F i), (A i).symm.trans (B i)) := by
    exact Int.inductionOn'_add_one hi
  have hXpred (i : ℤ) (hi : i ≤ k) :
      X (i - 1) = ((D (i - 1)).trans (F i), (A (i - 1)).trans (B i)) := by
    exact Int.inductionOn'_sub_one hi
  have hFk : F k = Diffeomorph.refl J RoundCylinderSpace ∞ :=
    congrArg Prod.fst hXbase
  have hBk : B k = Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞ :=
    congrArg Prod.snd hXbase
  have hFs (i : ℤ) (hi : k ≤ i) : F (i + 1) = (D i).symm.trans (F i) :=
    congrArg Prod.fst (hXsucc i hi)
  have hBs (i : ℤ) (hi : k ≤ i) : B (i + 1) = (A i).symm.trans (B i) :=
    congrArg Prod.snd (hXsucc i hi)
  have hFp (i : ℤ) (hi : i ≤ k) : F (i - 1) = (D (i - 1)).trans (F i) :=
    congrArg Prod.fst (hXpred i hi)
  have hBp (i : ℤ) (hi : i ≤ k) : B (i - 1) = (A (i - 1)).trans (B i) :=
    congrArg Prod.snd (hXpred i hi)
  have hrec (i : ℤ) : F i = (D i).trans (F (i + 1)) ∧
      B i = (A i).trans (B (i + 1)) := by
    by_cases hi : k ≤ i
    · rw [hFs i hi, hBs i hi]
      constructor
      · apply Diffeomorph.ext
        intro z
        simp only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.symm_apply_apply]
      · apply Diffeomorph.ext
        intro q
        simp only [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.symm_apply_apply]
    · have hj : i + 1 ≤ k := by omega
      simpa only [add_sub_cancel_right] using And.intro (hFp (i + 1) hj) (hBp (i + 1) hj)
  have hDi (i : ℤ) (z : RoundCylinderSpace) :
      ((D i).symm z).1 = (A i).symm z.1 := by
    apply (A i).injective
    change A i ((D i).symm z).1 = A i ((A i).symm z.1)
    rw [← hfirst i ((D i).symm z), Diffeomorph.apply_symm_apply,
      Diffeomorph.apply_symm_apply]
  have hDpair (i : ℤ) (q : UnitTwoSphere) (s : ℝ) :
      D i (q, s) = (A i q, (D i (q, s)).2) :=
    Prod.ext (hfirst i (q, s)) rfl
  have hDipair (i : ℤ) (q : UnitTwoSphere) (s : ℝ) :
      (D i).symm (q, s) = ((A i).symm q, ((D i).symm (q, s)).2) :=
    Prod.ext (hDi i (q, s)) rfl
  have hDimono (i : ℤ) (q : UnitTwoSphere) :
      StrictMono (fun s : ℝ => ((D i).symm (q, s)).2) := by
    intro s t hst
    by_contra h
    have hle := (hmono i ((A i).symm q)).monotone (le_of_not_gt h)
    have he (r : ℝ) :
        D i ((A i).symm q, ((D i).symm (q, r)).2) = (q, r) := by
      rw [← hDipair i q r]
      exact (D i).apply_symm_apply (q, r)
    rw [he t, he s] at hle
    exact (not_le_of_gt hst) hle
  have hFfirst (i : ℤ) : ∀ z : RoundCylinderSpace, (F i z).1 = B i z.1 := by
    refine Int.inductionOn' i k ?_ ?_ ?_
    · intro z
      rw [hFk, hBk]
      rfl
    · intro j hj ih z
      rw [hFs j hj, hBs j hj]
      change (F j ((D j).symm z)).1 = B j ((A j).symm z.1)
      rw [ih, hDi]
    · intro j hj ih z
      rw [hFp j hj, hBp j hj]
      change (F j (D (j - 1) z)).1 = B j (A (j - 1) z.1)
      rw [ih, hfirst]
  have hFfirstInv (i : ℤ) (z : RoundCylinderSpace) :
      ((F i).symm z).1 = (B i).symm z.1 := by
    apply (B i).injective
    change B i ((F i).symm z).1 = B i ((B i).symm z.1)
    rw [← hFfirst i ((F i).symm z), Diffeomorph.apply_symm_apply,
      Diffeomorph.apply_symm_apply]
  have hFmono (i : ℤ) : ∀ q : UnitTwoSphere,
      StrictMono (fun s : ℝ => (F i (q, s)).2) := by
    refine Int.inductionOn' i k ?_ ?_ ?_
    · intro q s t hst
      simpa only [hFk, Diffeomorph.coe_refl, id_eq] using hst
    · intro j hj ih q s t hst
      rw [hFs j hj]
      change (F j ((D j).symm (q, s))).2 < (F j ((D j).symm (q, t))).2
      rw [hDipair j q s, hDipair j q t]
      exact ih ((A j).symm q) (hDimono j q hst)
    · intro j hj ih q s t hst
      rw [hFp j hj]
      change (F j (D (j - 1) (q, s))).2 < (F j (D (j - 1) (q, t))).2
      rw [hDpair (j - 1) q s, hDpair (j - 1) q t]
      exact ih (A (j - 1) q) (hmono (j - 1) q hst)
  let cu : ℝ := 9 * L / 16
  let cd : ℝ := 5 * L / 8
  let cU : ℤ → UnitTwoSphere → ℝ := fun i q => (F i (q, cu)).2 - cu
  let cD : ℤ → UnitTwoSphere → ℝ := fun i q => (F i (q, cd)).2 - cd
  have hInvUpper (i : ℤ) (q : UnitTwoSphere) (s : ℝ) (hs : cu ≤ s) :
      (D i).symm (q, s) = ((A i).symm q, s - p i ((A i).symm q)) := by
    have hp := (hshift i ((A i).symm q)).2
    have harg : 13 * L / 16 ≤ s - p i ((A i).symm q) := by
      dsimp only [cu] at hs
      linarith
    apply (D i).injective
    change D i ((D i).symm (q, s)) = D i ((A i).symm q, s - p i ((A i).symm q))
    rw [Diffeomorph.apply_symm_apply, hupper i _ _ harg]
    simp only [Diffeomorph.apply_symm_apply, sub_add_cancel]
  have hU (i : ℤ) (hi : k ≤ i) :
      (∀ q : UnitTwoSphere, ∀ s : ℝ, cu ≤ s → F i (q, s) = (B i q, s + cU i q)) ∧
      (∀ q : UnitTwoSphere, ((i - k : ℤ) : ℝ) * (9 * L / 32) ≤ cU i q) := by
    refine Int.leInduction (motive := fun i _ =>
      (∀ q : UnitTwoSphere, ∀ s : ℝ, cu ≤ s → F i (q, s) = (B i q, s + cU i q)) ∧
      (∀ q : UnitTwoSphere, ((i - k : ℤ) : ℝ) * (9 * L / 32) ≤ cU i q)) ?_ ?_ i hi
    · simp only [cU, hFk, hBk, Diffeomorph.coe_refl, id_eq, sub_self,
        add_zero, Int.cast_zero, zero_mul, le_refl, implies_true, and_self]
    · intro j hj ih
      have hform (q : UnitTwoSphere) (s : ℝ) (hs : cu ≤ s) :
          F (j + 1) (q, s) =
            (B (j + 1) q, s + (cU j ((A j).symm q) - p j ((A j).symm q))) := by
        rw [hFs j hj]
        change F j ((D j).symm (q, s)) = _
        rw [hInvUpper j q s hs]
        have harg : cu ≤ s - p j ((A j).symm q) := by
          have hp := (hshift j ((A j).symm q)).2
          linarith
        rw [ih.1 _ _ harg]
        apply Prod.ext
        · rw [hBs j hj]
          rfl
        · dsimp only [Prod.snd]
          ring
      have hc (q : UnitTwoSphere) :
          cU (j + 1) q = cU j ((A j).symm q) - p j ((A j).symm q) := by
        change (F (j + 1) (q, cu)).2 - cu = _
        rw [hform q cu le_rfl]
        dsimp only [Prod.snd]
        ring
      constructor
      · intro q s hs
        rw [hc]
        exact hform q s hs
      · intro q
        rw [hc]
        have hh := ih.2 ((A j).symm q)
        have hp := (hshift j ((A j).symm q)).2
        simp only [Int.cast_sub, Int.cast_add, Int.cast_one] at hh ⊢
        nlinarith
  have hV (i : ℤ) (hi : i ≤ k) :
      (∀ q : UnitTwoSphere, ∀ s : ℝ, s ≤ cd → F i (q, s) = (B i q, s + cD i q)) ∧
      (∀ q : UnitTwoSphere, cD i q ≤ -(((k - i : ℤ) : ℝ) * (3 * L / 16))) := by
    refine Int.leInductionDown (motive := fun i _ =>
      (∀ q : UnitTwoSphere, ∀ s : ℝ, s ≤ cd → F i (q, s) = (B i q, s + cD i q)) ∧
      (∀ q : UnitTwoSphere, cD i q ≤ -(((k - i : ℤ) : ℝ) * (3 * L / 16)))) ?_ ?_ i hi
    · simp only [cD, hFk, hBk, Diffeomorph.coe_refl, id_eq, sub_self,
        add_zero, Int.cast_zero, zero_mul, neg_zero, le_refl, implies_true, and_self]
    · intro j hj ih
      have hform (q : UnitTwoSphere) (s : ℝ) (hs : s ≤ cd) :
          F (j - 1) (q, s) =
            (B (j - 1) q, s + (m (j - 1) q + cD j (A (j - 1) q))) := by
        rw [hFp j hj]
        change F j (D (j - 1) (q, s)) = _
        have hs0 : s ≤ 11 * L / 16 := by
          dsimp only [cd] at hs
          linarith
        rw [hlower (j - 1) q s hs0]
        have harg : s + m (j - 1) q ≤ cd := by
          have hm := (hshift (j - 1) q).1
          linarith
        rw [ih.1 _ _ harg]
        apply Prod.ext
        · rw [hBp j hj]
          rfl
        · dsimp only [Prod.snd]
          ring
      have hc (q : UnitTwoSphere) :
          cD (j - 1) q = m (j - 1) q + cD j (A (j - 1) q) := by
        change (F (j - 1) (q, cd)).2 - cd = _
        rw [hform q cd le_rfl]
        dsimp only [Prod.snd]
        ring
      constructor
      · intro q s hs
        rw [hc]
        exact hform q s hs
      · intro q
        rw [hc]
        have hh := ih.2 (A (j - 1) q)
        have hm := (hshift (j - 1) q).1
        simp only [Int.cast_sub, Int.cast_one] at hh ⊢
        nlinarith
  let c : ℤ → UnitTwoSphere → ℝ := fun i => if k ≤ i then cU i else cD i
  have hcSmooth (i : ℤ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (c i) := by
    have heval (t : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun q : UnitTwoSphere => (F i (q, t)).2 - t) :=
      (contDiff_id.sub contDiff_const).contMDiff.comp
        (contMDiff_snd.comp ((F i).contMDiff.comp (contMDiff_id.prodMk contMDiff_const)))
    dsimp only [c]
    split_ifs
    · exact heval cu
    · exact heval cd
  refine ⟨F, B, c, hFk, hBk, hrec, fun i z => ⟨hFfirst i z, hFfirstInv i z⟩,
    hFmono, hcSmooth, ?_, ?_⟩
  · intro i hi
    simpa only [c, if_pos hi] using hU i hi
  · intro i hi
    by_cases hki : k ≤ i
    · have hik : i = k := le_antisymm hi hki
      subst i
      simpa only [c, if_pos le_rfl, cU, cD, hFk, Diffeomorph.coe_refl,
        id_eq, sub_self] using hV k le_rfl
    · simpa only [c, if_neg hki] using hV i hi

end PoincareConjecture
