import PoincareConjecture.Proofs.M25.Topology3D.Plane.BumpFiber
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CompactConjugation

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_relative_openTube_graph_transport
    (T : OpenPartialHomeomorph
      ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)))
    {U K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {w A R : ℝ} (hA : 0 < A) (hAw : A < w) (_hR : 0 < R)
    (hsource : T.source = U ×ˢ {q : ℝ × ℝ | |q.2| < w})
    (hparameter : ∀ p, (T p).1 = p.1)
    (hT : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (g : (ℝ × ℝ) × ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hbound : ∀ p, |g p| < A)
    (hzero : ∀ z u, z ∉ K ∨ R ≤ |u| → g (z, u) = 0) :
    ∃ F : (ℝ × ℝ) → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (F p.1).symm p.2) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z q, q ∉ Q → F z q = q ∧ (F z).symm q = q) ∧
      (∀ z, HasCompactSupport (fun q => F z q - q) ∧
        HasCompactSupport (fun q => (F z).symm q - q)) ∧
      (∀ z, (∀ u, g (z, u) = 0) → ∀ q, F z q = q ∧ (F z).symm q = q) ∧
      ∀ z ∈ U, ∀ u, F z (T (z, (u, 0))).2 = (T (z, (u, g (z, u)))).2 := by
  let r := (w - A) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hwidth : A + r < w := by dsimp [r]; linarith
  obtain ⟨β, B, hB, hβ, hβ0, _, hβsupport, hβderiv⟩ := exists_smooth_fiber_cutoff hr
  obtain ⟨n, hn⟩ := exists_nat_gt (B * A)
  have hn0 : (0 : ℝ) < n := (mul_pos hB hA).trans hn
  let d : (ℝ × ℝ) × ℝ → ℝ := fun p => g p / n
  have hd : ContDiff ℝ ∞ d := hg.div_const _
  have hdabs (p : (ℝ × ℝ) × ℝ) : |d p| < A / n := by
    rw [show |d p| = |g p| / n by simp only [d, abs_div, abs_of_pos hn0]]
    exact div_lt_div_of_pos_right (hbound p) hn0
  have hsmall (p : (ℝ × ℝ) × ℝ) : B * |d p| < 1 := by
    calc
      B * |d p| < B * (A / n) := mul_lt_mul_of_pos_left (hdabs p) hB
      _ = B * A / n := by ring
      _ < 1 := (div_lt_iff₀ hn0).2 (by simpa only [one_mul] using hn)
  let C : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    K ×ˢ (Icc (-R) R ×ˢ Icc (-A - r) (A + r))
  have hC : IsCompact C := hK.prod (isCompact_Icc.prod isCompact_Icc)
  have hCs : C ⊆ T.source := by
    intro p hp
    rw [hsource]
    refine ⟨hKU hp.1, ?_⟩
    have hnormal : |p.2.2| ≤ A + r := abs_le.mpr ⟨by linarith [hp.2.2.1], hp.2.2.2⟩
    exact hnormal.trans_lt hwidth
  let S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := T '' C
  have hS : IsCompact S := hC.image_of_continuousOn (T.continuousOn.mono hCs)
  have hStarget : S ⊆ T.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact T.map_source (hCs hp)
  have hInvparameter (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∈ T.target) :
      (T.symm p).1 = p.1 := by
    simpa only [hparameter] using congrArg Prod.fst (T.right_inv hp)
  have hratio (k : ℕ) (hk : k ≤ n) : 0 ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg k) hn0.le
    · apply (div_le_iff₀ hn0).2
      simp only [one_mul]
      exact_mod_cast hk
  have hind : ∀ k : ℕ, k ≤ n →
      ∃ Φ : ((ℝ × ℝ) × (ℝ × ℝ)) ≃ₘ[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)),
        (∀ p, (Φ p).1 = p.1 ∧ (Φ.symm p).1 = p.1) ∧
        (∀ p, p ∉ S → Φ p = p ∧ Φ.symm p = p) ∧
        (∀ z, (∀ u, g (z, u) = 0) → ∀ q, Φ (z, q) = (z, q) ∧
          Φ.symm (z, q) = (z, q)) ∧
        ∀ z ∈ U, ∀ u,
          Φ (T (z, (u, 0))) = T (z, (u, (k : ℝ) / n * g (z, u))) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Diffeomorph.refl 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) _ ∞,
        (fun _ => ⟨rfl, rfl⟩), (fun _ _ => ⟨rfl, rfl⟩),
        (fun _ _ _ => ⟨rfl, rfl⟩), ?_⟩
      intro z _ u
      simp only [Diffeomorph.coe_refl, id_eq, Nat.cast_zero, zero_div, zero_mul]
    | succ k ih =>
      intro hk
      have hkn : k ≤ n := by omega
      obtain ⟨Φ, hΦparameter, hΦfix, hΦzero, hΦgraph⟩ := ih hkn
      let a : (ℝ × ℝ) × ℝ → ℝ := fun p => (k : ℝ) / n * g p
      have ha : ContDiff ℝ ∞ a := contDiff_const.mul hg
      have habound (p : (ℝ × ℝ) × ℝ) : |a p| ≤ A := by
        simp only [a, abs_mul, abs_of_nonneg (hratio k hkn).1]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hratio k hkn).2).trans (hbound p).le
      obtain ⟨D, hD, _, hDtail, hDgraph⟩ := exists_smooth_bump_fiber_diffeomorph
        β hβ hβ0 a d ha hd hβderiv hsmall habound hβsupport
      let e : (((ℝ × ℝ) × ℝ) × ℝ) ≃ₘ[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) :=
        (ContinuousLinearEquiv.prodAssoc ℝ (ℝ × ℝ) ℝ ℝ).toDiffeomorph
      let L := e.symm.trans (D.trans e)
      have hL (p : (ℝ × ℝ) × (ℝ × ℝ)) :
          L p = (p.1, (p.2.1, p.2.2 + β (p.2.2 - a (p.1, p.2.1)) *
            d (p.1, p.2.1))) := by
        change e (D ((p.1, p.2.1), p.2.2)) = _
        rw [hD]
        rfl
      have hLparameter (p : (ℝ × ℝ) × (ℝ × ℝ)) : (L p).1 = p.1 := by
        rw [hL]
      have hLfix (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∉ C) : L p = p := by
        by_cases hz : p.1 ∈ K
        · by_cases hu : p.2.1 ∈ Icc (-R) R
          · have hy : p.2.2 ∉ Icc (-A - r) (A + r) := fun hy => hp ⟨hz, hu, hy⟩
            have htail : p.2.2 ≤ -A - r ∨ A + r ≤ p.2.2 := by
              by_cases hlow : -A - r ≤ p.2.2
              · exact Or.inr (lt_of_not_ge (fun hhi => hy ⟨hlow, hhi⟩)).le
              · exact Or.inl (lt_of_not_ge hlow).le
            change e (D ((p.1, p.2.1), p.2.2)) = p
            rw [hDtail _ _ htail]
            rfl
          · have habs : R ≤ |p.2.1| := by
              by_contra hnR
              exact hu (by rcases abs_lt.mp (lt_of_not_ge hnR) with ⟨hl, hr⟩
                           exact ⟨hl.le, hr.le⟩)
            rw [hL]
            simp only [d, hzero p.1 p.2.1 (Or.inr habs), zero_div, mul_zero,
              add_zero, Prod.mk.eta]
        · rw [hL]
          simp only [d, hzero p.1 p.2.1 (Or.inl hz), zero_div, mul_zero,
            add_zero, Prod.mk.eta]
      have hLzero (z : ℝ × ℝ) (hz : ∀ u, g (z, u) = 0) (q : ℝ × ℝ) :
          L (z, q) = (z, q) := by
        rw [hL]
        simp only [d, hz, zero_div, mul_zero, add_zero, Prod.mk.eta]
      obtain ⟨Ψ, hΨ, _, hΨfix, hΨInvfix, _, _⟩ :=
        exists_compact_tube_conjugate T hT hInv L hC hCs hLfix
      have hΨparameter (p : (ℝ × ℝ) × (ℝ × ℝ)) : (Ψ p).1 = p.1 := by
        by_cases hp : p ∈ T.target
        · rw [hΨ p hp, hparameter, hLparameter, hInvparameter p hp]
        · rw [hΨfix p (fun h => hp (hStarget h))]
      have hΨInvparameter (p : (ℝ × ℝ) × (ℝ × ℝ)) :
          (Ψ.symm p).1 = p.1 := by
        simpa only [Ψ.apply_symm_apply] using (hΨparameter (Ψ.symm p)).symm
      have hΨzero (z : ℝ × ℝ) (hz : ∀ u, g (z, u) = 0) (q : ℝ × ℝ) :
          Ψ (z, q) = (z, q) := by
        by_cases hp : (z, q) ∈ T.target
        · have hpz : (T.symm (z, q)).1 = z := hInvparameter (z, q) hp
          have hLp : L (T.symm (z, q)) = T.symm (z, q) := by
            have heq : T.symm (z, q) = (z, (T.symm (z, q)).2) := Prod.ext hpz rfl
            calc
              L (T.symm (z, q)) = L (z, (T.symm (z, q)).2) := congrArg L heq
              _ = (z, (T.symm (z, q)).2) := hLzero z hz _
              _ = T.symm (z, q) := heq.symm
          rw [hΨ _ hp, hLp, T.right_inv hp]
        · exact hΨfix _ (fun h => hp (hStarget h))
      have hΨInvzero (z : ℝ × ℝ) (hz : ∀ u, g (z, u) = 0) (q : ℝ × ℝ) :
          Ψ.symm (z, q) = (z, q) := by
        have h := congrArg Ψ.symm (hΨzero z hz q)
        simpa only [Ψ.symm_apply_apply] using h.symm
      have hstep (z : ℝ × ℝ) (hz : z ∈ U) (u : ℝ) :
          Ψ (T (z, (u, a (z, u)))) = T (z, (u, a (z, u) + d (z, u))) := by
        have hs : (z, (u, a (z, u))) ∈ T.source := by
          rw [hsource]
          exact ⟨hz, (habound (z, u)).trans_lt hAw⟩
        rw [hΨ _ (T.map_source hs), T.left_inv hs]
        change T (e (D ((z, u), a (z, u)))) = _
        rw [hDgraph]
        rfl
      refine ⟨Φ.trans Ψ, ?_, ?_, ?_, ?_⟩
      · intro p
        constructor
        · change (Ψ (Φ p)).1 = p.1
          rw [hΨparameter, (hΦparameter p).1]
        · change (Φ.symm (Ψ.symm p)).1 = p.1
          rw [(hΦparameter _).2, hΨInvparameter]
      · intro p hp
        change Ψ (Φ p) = p ∧ Φ.symm (Ψ.symm p) = p
        rw [(hΦfix p hp).1, hΨfix p hp, hΨInvfix p hp, (hΦfix p hp).2]
        exact ⟨rfl, rfl⟩
      · intro z hz q
        change Ψ (Φ (z, q)) = (z, q) ∧ Φ.symm (Ψ.symm (z, q)) = (z, q)
        rw [(hΦzero z hz q).1, hΨzero z hz q, hΨInvzero z hz q,
          (hΦzero z hz q).2]
        exact ⟨rfl, rfl⟩
      · intro z hz u
        have hsum : a (z, u) + d (z, u) = ((k + 1 : ℕ) : ℝ) / n * g (z, u) := by
          simp only [a, d, Nat.cast_add, Nat.cast_one]
          ring
        change Ψ (Φ (T (z, (u, 0)))) = _
        rw [hΦgraph z hz u]
        change Ψ (T (z, (u, a (z, u)))) = _
        rw [hstep z hz u, hsum]
  obtain ⟨Φ, hΦparameter, hΦfix, hΦzero, hΦgraph⟩ := hind n le_rfl
  let f : (ℝ × ℝ) → (ℝ × ℝ) → ℝ × ℝ := fun z q => (Φ (z, q)).2
  let v : (ℝ × ℝ) → (ℝ × ℝ) → ℝ × ℝ := fun z q => (Φ.symm (z, q)).2
  have hforward (z q : ℝ × ℝ) : Φ (z, q) = (z, f z q) :=
    Prod.ext (hΦparameter (z, q)).1 rfl
  have hinverse (z q : ℝ × ℝ) : Φ.symm (z, q) = (z, v z q) :=
    Prod.ext (hΦparameter (z, q)).2 rfl
  have hleft (z : ℝ × ℝ) : LeftInverse (v z) (f z) := by
    intro q
    have h := congrArg Prod.snd (Φ.symm_apply_apply (z, q))
    rw [hforward] at h
    exact h
  have hright (z : ℝ × ℝ) : LeftInverse (f z) (v z) := by
    intro q
    have h := congrArg Prod.snd (Φ.apply_symm_apply (z, q))
    rw [hinverse] at h
    exact h
  let F : (ℝ × ℝ) → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) := fun z =>
    { toEquiv :=
        { toFun := f z
          invFun := v z
          left_inv := hleft z
          right_inv := hright z }
      contMDiff_toFun :=
        (Φ.contDiff.comp (contDiff_const.prodMk contDiff_id)).snd.contMDiff
      contMDiff_invFun :=
        (Φ.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)).snd.contMDiff }
  let Q : Set (ℝ × ℝ) := Prod.snd '' S
  have hQ : IsCompact Q := hS.image continuous_snd
  have hfixed (z q : ℝ × ℝ) (hq : q ∉ Q) : F z q = q ∧ (F z).symm q = q := by
    have hp : (z, q) ∉ S := fun h => hq ⟨(z, q), h, rfl⟩
    exact ⟨congrArg Prod.snd (hΦfix (z, q) hp).1,
      congrArg Prod.snd (hΦfix (z, q) hp).2⟩
  refine ⟨F, Φ.contDiff.snd, Φ.symm.contDiff.snd, ⟨Q, hQ, hfixed⟩, ?_, ?_, ?_⟩
  · intro z
    exact ⟨HasCompactSupport.intro hQ (fun q hq => sub_eq_zero.mpr (hfixed z q hq).1),
      HasCompactSupport.intro hQ (fun q hq => sub_eq_zero.mpr (hfixed z q hq).2)⟩
  · intro z hz q
    exact ⟨congrArg Prod.snd (hΦzero z hz q).1, congrArg Prod.snd (hΦzero z hz q).2⟩
  · intro z hz u
    have hp : (z, (T (z, (u, 0))).2) = T (z, (u, 0)) :=
      Prod.ext (hparameter (z, (u, 0))).symm rfl
    change (Φ (z, (T (z, (u, 0))).2)).2 = _
    rw [hp]
    simpa only [div_self hn0.ne', one_mul] using congrArg Prod.snd (hΦgraph z hz u)

end PoincareConjecture.M25.Topology3D
