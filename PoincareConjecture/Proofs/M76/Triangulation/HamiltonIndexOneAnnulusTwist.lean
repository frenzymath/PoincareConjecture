import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneCrossingArc
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "W" => (ℝ × V2)
local notation "C8" => AddCircle (4 * (2 : ℝ))

theorem exists_finitePL_annulus_twist (alpha : ℝ →ᴬ[ℝ] ℝ)
    (hminus : ((alpha (-1) : ℝ) : C8) = 0)
    (hplus : ((alpha 1 : ℝ) : C8) = 0) :
    ∃ e : (J ×ˢ Q) ≃ₜ (J ×ˢ Q), e.IsFinitePL ∧
      (∀ x : (J ×ˢ Q : Set W), (e x : W) =
        ((x : W).1, (squareCircle
          (squareCircle.symm ⟨(x : W).2, x.property.2⟩ +
            ((alpha (x : W).1 : ℝ) : C8)) : V2))) ∧
      ∀ x : (J ×ˢ Q : Set W), (x : W).1 = -1 ∨ (x : W).1 = 1 → e x = x := by
  classical
  let : Fact (0 < 4 * (2 : ℝ)) := ⟨by norm_num⟩
  let D : (J × Q) ≃ₜ (J × Q) :=
    { toFun := fun x => (x.1, squareCircle
        (squareCircle.symm x.2 + ((alpha (x.1 : ℝ) : ℝ) : C8)))
      invFun := fun x => (x.1, squareCircle
        (squareCircle.symm x.2 - ((alpha (x.1 : ℝ) : ℝ) : C8)))
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      continuous_toFun := continuous_fst.prodMk
        (squareCircle.continuous.comp
          ((squareCircle.symm.continuous.comp continuous_snd).add
            ((AddCircle.continuous_mk' _).comp
              (alpha.continuous.comp continuous_fst.subtype_val))))
      continuous_invFun := continuous_fst.prodMk
        (squareCircle.continuous.comp
          ((squareCircle.symm.continuous.comp continuous_snd).sub
            ((AddCircle.continuous_mk' _).comp
              (alpha.continuous.comp continuous_fst.subtype_val)))) }
  let e := (Homeomorph.Set.prod J Q).trans (D.trans (Homeomorph.Set.prod J Q).symm)
  have heval (x : (J ×ˢ Q : Set W)) : (e x : W) =
      ((x : W).1, (squareCircle (squareCircle.symm ⟨(x : W).2, x.property.2⟩ +
        ((alpha (x : W).1 : ℝ) : C8)) : V2)) := rfl
  let F : W → W := fun p => if hp : p ∈ J ×ˢ Q then e ⟨p, hp⟩ else p
  have hF (p : W) (hp : p ∈ J ×ˢ Q) : F p =
      (p.1, (squareCircle (squareCircle.symm ⟨p.2, hp.2⟩ +
        ((alpha p.1 : ℝ) : C8)) : V2)) := by
    simp only [F, dif_pos hp]
    exact heval ⟨p, hp⟩
  let b : (ℝ × ℝ) → W := fun p => (p.1, (squareCircle ((p.2 : ℝ) : C8) : V2))
  let rect (c : ℝ) : Set (ℝ × ℝ) := J ×ˢ Icc c (c + 4)
  have hrect (c : ℝ) : IsFinitePLBallPair (ℝ × ℝ) (rect c)
      ((({-1, 1} : Set ℝ) ×ˢ Icc c (c + 4)) ∪ (J ×ˢ {c, c + 4})) :=
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
      (isFinitePLBallPair_Icc (by linarith : c < c + 4))
  have hb (c : ℝ) : FinitePiecewiseAffineOn b (rect c) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hrect c
    have hs : FinitePiecewiseAffineOn Prod.fst (rect c) :=
      ⟨K, hK, hKs, K.affineOnFaces_affine
        (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap⟩
    have ht : FinitePiecewiseAffineOn Prod.snd (rect c) :=
      ⟨K, hK, hKs, K.affineOnFaces_affine
        (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap⟩
    exact hs.prod_mk (finitePiecewiseAffineOn_squareCircle_comp ht)
  have hbinj (c : ℝ) : InjOn b (rect c) := by
    intro x hx y hy hxy
    have hs : x.1 = y.1 := by
      simpa only [b] using congrArg (Prod.fst : W → ℝ) hxy
    have ht : (x.2 : C8) = (y.2 : C8) := by
      apply squareCircle.injective
      apply Subtype.ext
      exact congrArg (Prod.snd : W → V2) hxy
    have hxi : x.2 ∈ Ico c (c + 4 * (2 : ℝ)) :=
      ⟨hx.2.1, by linarith [hx.2.2]⟩
    have hyi : y.2 ∈ Ico c (c + 4 * (2 : ℝ)) :=
      ⟨hy.2.1, by linarith [hy.2.2]⟩
    exact Prod.ext hs ((AddCircle.coe_eq_coe_iff_of_mem_Ico hxi hyi).mp ht)
  have hbmem (c : ℝ) {p : ℝ × ℝ} (hp : p ∈ rect c) : b p ∈ J ×ˢ Q :=
    ⟨hp.1, (squareCircle _).property⟩
  have hFb (c : ℝ) : FinitePiecewiseAffineOn (F ∘ b) (rect c) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hrect c
    let s : (ℝ × ℝ) →ᴬ[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
    let t : (ℝ × ℝ) →ᴬ[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
    have hs : FinitePiecewiseAffineOn s (rect c) :=
      ⟨K, hK, hKs, K.affineOnFaces_affine s⟩
    have hang : FinitePiecewiseAffineOn (t + alpha.comp s) (rect c) :=
      ⟨K, hK, hKs, K.affineOnFaces_affine (t + alpha.comp s)⟩
    apply (hs.prod_mk (finitePiecewiseAffineOn_squareCircle_comp hang)).congr
    intro p hp
    change (p.1, (squareCircle (((p.2 + alpha p.1 : ℝ)) : C8) : V2)) = F (b p)
    rw [hF _ (hbmem c hp)]
    simp only [b, squareCircle.symm_apply_apply, AddCircle.coe_add]
  have hFimage (c : ℝ) : FinitePiecewiseAffineOn F (b '' rect c) := by
    obtain ⟨g, hg, hgeq⟩ := (hb c).exists_homeomorph_image (hbinj c)
    obtain ⟨r, hr, hreq⟩ := hg.symm
    have hrmem {x : W} (hx : x ∈ b '' rect c) : r x ∈ rect c := by
      rw [← hreq ⟨x, hx⟩]
      exact (g.symm ⟨x, hx⟩).property
    have hbr {x : W} (hx : x ∈ b '' rect c) : b (r x) = x := by
      rw [← hreq ⟨x, hx⟩, ← hgeq, g.apply_symm_apply]
    apply ((hFb c).comp hr (fun _ hx => hrmem hx)).congr
    intro x hx
    change F (b (r x)) = F x
    rw [hbr hx]
  have hcover : (b '' rect 0) ∪ (b '' rect 4) = J ×ˢ Q := by
    ext x
    constructor
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · exact hbmem 0 hp
      · exact hbmem 4 hp
    · intro hx
      let q : Q := ⟨x.2, hx.2⟩
      let t : ℝ := AddCircle.equivIco (4 * (2 : ℝ)) 0 (squareCircle.symm q)
      have ht : t ∈ Ico (0 : ℝ) 8 := by
        have ht0 : t ∈ Ico (0 : ℝ) (4 * (2 : ℝ)) := by
          simpa only [zero_add] using
            (AddCircle.equivIco (4 * (2 : ℝ)) 0 (squareCircle.symm q)).property
        norm_num at ht0
        exact ht0
      have htq : squareCircle ((t : ℝ) : C8) = q := by
        rw [AddCircle.coe_equivIco, squareCircle.apply_symm_apply]
      have hbx : b (x.1, t) = x := by
        apply Prod.ext
        · rfl
        · exact congrArg Subtype.val htq
      by_cases ht4 : t ≤ 4
      · exact Or.inl ⟨(x.1, t), ⟨hx.1, ht.1, by simpa using ht4⟩, hbx⟩
      · exact Or.inr ⟨(x.1, t), ⟨hx.1, (lt_of_not_ge ht4).le,
          by linarith [ht.2]⟩, hbx⟩
  have hFPL : FinitePiecewiseAffineOn F (J ×ˢ Q) :=
    hcover ▸ finitePiecewiseAffineOn_union (hFimage 0) (hFimage 4)
  refine ⟨e, ⟨F, hFPL, ?_⟩, heval, ?_⟩
  · intro x
    simp only [F, dif_pos x.property]
  · intro x hx
    apply Subtype.ext
    rw [heval]
    have ha : ((alpha (x : W).1 : ℝ) : C8) = 0 := by
      rcases hx with hx | hx
      · rw [hx, hminus]
      · rw [hx, hplus]
    rw [ha, add_zero, squareCircle.apply_symm_apply]

theorem exists_zero_winding_marked_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : Set E} (tau : (J ×ˢ Q) ≃ₜ T) (htau : tau.IsFinitePL)
    (rho : C(J × Q, Q))
    (hminus : ∀ u : Q, rho (⟨-1, by norm_num⟩, u) = u)
    (hplus : ∀ u : Q, rho (⟨1, by norm_num⟩, u) = u) :
    ∃ (m : ℤ) (marked : (J ×ˢ Q) ≃ₜ T) (f : ℝ → E) (ell : C(J, ℝ)),
      marked.IsFinitePL ∧ FinitePiecewiseAffineOn f J ∧ InjOn f J ∧
      (∀ s : J, f s = marked ⟨((s : ℝ), (squareCircle (0 : C8) : V2)),
        s.property, (squareCircle _).property⟩) ∧
      (∀ s : J, f s = tau ⟨((s : ℝ),
        (squareCircle ((-4 * (m : ℝ) * ((s : ℝ) + 1) : ℝ) : C8) : V2)),
          s.property, (squareCircle _).property⟩) ∧
      (∀ x : (J ×ˢ Q : Set W), (x : W).1 = -1 ∨ (x : W).1 = 1 → marked x = tau x) ∧
      f (-1) = tau ⟨(-1, (squareCircle (0 : C8) : V2)),
        by norm_num, (squareCircle _).property⟩ ∧
      f 1 = tau ⟨(1, (squareCircle (0 : C8) : V2)),
        by norm_num, (squareCircle _).property⟩ ∧
      ell ⟨-1, by norm_num⟩ = 0 ∧ ell ⟨1, by norm_num⟩ = 0 ∧
      ∀ s : J,
        rho (s, squareCircle ((-4 * (m : ℝ) * ((s : ℝ) + 1) : ℝ) : C8)) =
          squareCircle ((ell s : ℝ) : C8) := by
  obtain ⟨m, f, ell, hf, hfinj, hfval, hfm, hfp, helm, help, hangle⟩ :=
    exists_zero_winding_crossing_arc tau htau rho hminus hplus
  let alpha : ℝ →ᴬ[ℝ] ℝ := (-4 * (m : ℝ)) •
    (ContinuousAffineMap.id ℝ ℝ + ContinuousAffineMap.const ℝ ℝ 1)
  have ha (s : ℝ) : alpha s = -4 * (m : ℝ) * (s + 1) := rfl
  have ham : ((alpha (-1) : ℝ) : C8) = 0 := by simp [ha]
  have hap : ((alpha 1 : ℝ) : C8) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (4 * (2 : ℝ))).mpr
    refine ⟨-m, ?_⟩
    rw [ha, zsmul_eq_mul, Int.cast_neg]
    ring
  obtain ⟨e, he, heval, hef⟩ := exists_finitePL_annulus_twist alpha ham hap
  let marked := e.trans tau
  refine ⟨m, marked, f, ell, he.trans htau, hf, hfinj, ?_, hfval, ?_,
    hfm, hfp, helm, help, hangle⟩
  · intro s
    rw [hfval s]
    change (tau _ : E) = (tau (e _): E)
    apply congrArg (fun x : (J ×ˢ Q : Set W) => (tau x : E))
    apply Subtype.ext
    rw [heval]
    simp only [squareCircle.symm_apply_apply, zero_add, ha]
  · intro x hx
    change tau (e x) = tau x
    rw [hef x hx]

end PoincareConjecture.M76.HamiltonIndexOne
