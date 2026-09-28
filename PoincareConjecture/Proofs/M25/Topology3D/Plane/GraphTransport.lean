import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeGraphSlide
import PoincareConjecture.Proofs.M25.Topology3D.Plane.HeightExtension
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TimePreservingFibers

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_curveAnnularTube_graph_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {L U w : ℝ} (hw : w < 1)
    (hs : T.source = Ioo L U ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ p : ℝ × E, T p = (p.1, curveAnnularExtension o q0 c p))
    (hfwd : ContDiffOn ℝ ∞ T T.source) (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    {a b A : ℝ} (ha : L < a) (hb : b < U) (hAw : A < w)
    (g : ℝ × sphere (0 : E) 1 → ℝ)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ g)
    (hbound : ∀ p, |g p| < A) :
    ∃ F : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
      (∃ K : Set E, IsCompact K ∧
        ∀ z x, x ∉ K → F z x = x ∧ (F z).symm x = x) ∧
      (∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x)) ∧
      ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
        F z (c z q) = c z q + g (z, q) •
          curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ E = 2)]
    norm_num)
  have hA : 0 < A := (abs_nonneg (g (0, q0))).trans_lt (hbound (0, q0))
  let r := (w - A) / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hwidth : A + r < w := by
    dsimp [r]
    linarith
  obtain ⟨β, B, hB, hβ, hβ0, _, hβsupport, hβderiv⟩ := exists_smooth_fiber_cutoff hr
  obtain ⟨H, hH, hHsphere, hHbound, _⟩ :=
    exists_smooth_ambient_height_extension q0 g hg hbound
  let ε := min (a - L) (U - b) / 2
  have hε : 0 < ε := div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (by norm_num)
  let l := a - ε
  let u := b + ε
  have hl : L < l := by
    dsimp [l, ε]
    linarith [min_le_left (a - L) (U - b)]
  have hu : u < U := by
    dsimp [u, ε]
    linarith [min_le_right (a - L) (U - b)]
  obtain ⟨τ, hτ, hτrange, hτone, hτzero⟩ := exists_smooth_interval_cutoff a b hε
  obtain ⟨n, hn⟩ := exists_nat_gt (B * A)
  have hn0 : (0 : ℝ) < n := (mul_pos hB hA).trans hn
  let d : ℝ × E → ℝ := fun p => τ p.1 * H p / n
  have hd : ContDiff ℝ ∞ d := ((hτ.comp contDiff_fst).mul hH).div_const _
  have hdabs (p : ℝ × E) : |d p| < A / n := by
    have heq : |d p| = τ p.1 * |H p| / n := by
      simp only [d, abs_div, abs_mul, abs_of_nonneg (hτrange p.1).1, abs_of_pos hn0]
    rw [heq]
    exact div_lt_div_of_pos_right
      ((mul_le_of_le_one_left (abs_nonneg _) (hτrange p.1).2).trans_lt (hHbound p)) hn0
  have hsmall (p : ℝ × E) : B * |d p| < 1 := by
    calc
      B * |d p| < B * (A / n) := mul_lt_mul_of_pos_left (hdabs p) hB
      _ = B * A / n := by ring
      _ < 1 := (div_lt_iff₀ hn0).2 (by simpa only [one_mul] using hn)
  have htime (p : ℝ × E) (hp : p.1 ∉ Icc l u) : d p = 0 := by
    have ht : τ p.1 = 0 := by
      apply hτzero
      by_cases hlp : l ≤ p.1
      · right
        have hup : u < p.1 := lt_of_not_ge (fun h => hp ⟨hlp, h⟩)
        exact hup.le
      · exact Or.inl (lt_of_not_ge hlp).le
    simp only [d, ht, zero_mul, zero_div]
  let K : Set (ℝ × E) := Icc l u ×ˢ {x : E | |‖x‖ - 1| ≤ A + r}
  have hK : IsCompact K := isCompact_time_closedAnnulus l u (A + r)
  have hKs : K ⊆ T.source := by
    intro p hp
    rw [hs]
    exact ⟨⟨hl.trans_le hp.1.1, hp.1.2.trans_lt hu⟩, hp.2.trans_lt hwidth⟩
  let C : Set (ℝ × E) := T '' K
  have hC : IsCompact C := hK.image_of_continuousOn (T.continuousOn.mono hKs)
  have hratio (k : ℕ) (hk : k ≤ n) : 0 ≤ (k : ℝ) / n ∧ (k : ℝ) / n ≤ 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg k) hn0.le
    · apply (div_le_iff₀ hn0).2
      simp only [one_mul]
      exact_mod_cast hk
  have hind : ∀ k : ℕ, k ≤ n → ∃ Φ : (ℝ × E) ≃ₘ[ℝ] (ℝ × E),
      (∀ p, (Φ p).1 = p.1 ∧ (Φ.symm p).1 = p.1) ∧
      (∀ p, p ∉ C → Φ p = p ∧ Φ.symm p = p) ∧
      ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
        Φ (z, c z q) = (z, c z q + ((k : ℝ) / n * g (z, q)) •
          curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ × E) (ℝ × E) ∞,
        (fun _ => ⟨rfl, rfl⟩), (fun _ _ => ⟨rfl, rfl⟩), ?_⟩
      intro z _ q
      simp only [Diffeomorph.coe_refl, id_eq, Nat.cast_zero, zero_div, zero_mul,
        zero_smul, add_zero]
    | succ k ih =>
      intro hk
      have hkn : k ≤ n := by omega
      obtain ⟨Φ, hΦtime, hΦfix, hΦgraph⟩ := ih hkn
      let ak : ℝ × E → ℝ := fun p => (k : ℝ) / n * H p
      have hak : ContDiff ℝ ∞ ak := contDiff_const.mul hH
      have hakbound (p : ℝ × E) : |ak p| ≤ A := by
        simp only [ak, abs_mul, abs_of_nonneg (hratio k hkn).1]
        exact (mul_le_of_le_one_left (abs_nonneg _) (hratio k hkn).2).trans (hHbound p).le
      obtain ⟨Ψ, hΨtime, _, _, hΨfix, hΨgraph⟩ :=
        exists_curveAnnularTube_bump_slide o q0 c T hw hs he hfwd hInv
          β hβ hβ0 ak d hak hd hβderiv hsmall hakbound hβsupport hr hwidth hl hu htime
      refine ⟨Φ.trans Ψ, ?_, ?_, ?_⟩
      · intro p
        constructor
        · change (Ψ (Φ p)).1 = p.1
          rw [(hΨtime _).1, (hΦtime _).1]
        · change (Φ.symm (Ψ.symm p)).1 = p.1
          rw [(hΦtime _).2, (hΨtime _).2]
      · intro p hp
        change Ψ (Φ p) = p ∧ Φ.symm (Ψ.symm p) = p
        rw [(hΦfix p hp).1, (hΨfix p hp).1, (hΨfix p hp).2, (hΦfix p hp).2]
        exact ⟨rfl, rfl⟩
      · intro z hz q
        have hzI : z ∈ Ioo L U := ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩
        have hakq : ak (z, (q : E)) = (k : ℝ) / n * g (z, q) := by
          simp only [ak, hHsphere]
        have hsumq : ak (z, (q : E)) + d (z, (q : E)) =
            ((k + 1 : ℕ) : ℝ) / n * g (z, q) := by
          simp only [ak, d, hτone z hz, one_mul, hHsphere, Nat.cast_add, Nat.cast_one]
          ring
        have htarget : |ak (z, (q : E)) + d (z, (q : E))| < w := by
          rw [hsumq, abs_mul, abs_of_nonneg (hratio (k + 1) hk).1]
          exact ((mul_le_of_le_one_left (abs_nonneg _) (hratio (k + 1) hk).2).trans_lt
            (hbound (z, q))).trans hAw
        have hstep := hΨgraph z hzI q htarget
        rw [hsumq, hakq] at hstep
        change Ψ (Φ (z, c z q)) = _
        rw [hΦgraph z hz q]
        exact hstep
  obtain ⟨D, hDtime, hDfix, hDgraph⟩ := hind n le_rfl
  have hcompact : HasCompactSupport (fun p => D p - p) :=
    HasCompactSupport.intro hC (fun p hp => sub_eq_zero.mpr (hDfix p hp).1)
  obtain ⟨F, hF, _, hFsmooth, hInvsmooth, hKspatial, hFcompact⟩ :=
    exists_time_preserving_diffeomorph_fibers D (fun p => (hDtime p).1) hcompact
  refine ⟨F, hFsmooth, hInvsmooth, hKspatial, hFcompact, ?_⟩
  intro z hz q
  rw [hF]
  simpa only [div_self (ne_of_gt hn0), one_mul] using congrArg Prod.snd (hDgraph z hz q)

end PoincareConjecture.M25.Topology3D
