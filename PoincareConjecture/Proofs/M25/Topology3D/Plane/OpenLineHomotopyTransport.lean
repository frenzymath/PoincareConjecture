import PoincareConjecture.Proofs.M25.Topology3D.Plane.NearbyOpenLineTransport
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic








set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D



theorem exists_compact_openLine_homotopy_transport
    (D : (ℝ × ℝ) × ℝ → ℝ × ℝ) {R : ℝ} (hR : 0 < R)
    (hD : ContDiff ℝ ∞ D)
    (hinj : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      Injective (fun u : ℝ => D (z, u)))
    (hreg : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ u : ℝ,
      fderiv ℝ (fun v : ℝ => D (z, v)) u 1 ≠ 0)
    (htail : ∀ z u, R ≤ |u| → D (z, u) = (u, 0))
    (hstat : ∀ t s u, t ≤ 0 ∨ 1 ≤ t → D ((t, s), u) = D ((t, 0), u)) :
    ∃ G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (G p.1).symm p.2) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ t x, x ∉ Q → G t x = x ∧ (G t).symm x = x) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, G t x = x ∧ (G t).symm x = x) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        range (fun u : ℝ => G t (D ((t, 0), u))) =
          range (fun u : ℝ => D ((t, 1), u)) := by
  classical
  let I : Type := Icc (0 : ℝ) 1
  have hlocal (v : I) : ∃ r : ℝ, 0 < r ∧
      ∃ A : (ℝ × ℝ) → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
        ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => A p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (A p.1).symm p.2) ∧
        ∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
          (∀ z x, x ∉ Q → A z x = x ∧ (A z).symm x = x) ∧
          (∀ z, (∀ u, D (z, u) = D ((z.1, v.1), u)) →
            ∀ x, A z x = x ∧ (A z).symm x = x) ∧
          ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (v.1 - r) (v.1 + r),
            range (fun u : ℝ => A (t, s) (D ((t, v.1), u))) =
              range (fun u : ℝ => D ((t, s), u)) := by
    obtain ⟨r, hr, A, hA, hAi, ⟨Q, hQ, hfix⟩, _, hstatA, hArange⟩ :=
      exists_nearby_fixedTail_openLine_transport D (a := 0) (b := 1)
        (s0 := v.1) (R := R) (by norm_num) hR hD
        (fun t ht => hinj (t, v.1) ⟨ht, v.2⟩)
        (fun t ht u => hreg (t, v.1) ⟨ht, v.2⟩ u)
        htail
    refine ⟨r, hr, A, hA, hAi, Q, hQ, hfix, ?_, hArange⟩
    exact hstatA
  choose r hr A hA hAi Q hQ hfix hstatA hArange using hlocal
  let W : I → Set ℝ := fun v => Ioo (v.1 - r v) (v.1 + r v)
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ v : I, W v := by
    intro s hs
    refine mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩
    change s ∈ Ioo (s - r ⟨s, hs⟩) (s + r ⟨s, hs⟩)
    constructor <;> linarith [hr ⟨s, hs⟩]
  obtain ⟨ε, hε, hwindow⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun v => (isOpen_Ioo : IsOpen (W v))) hcover
  obtain ⟨N, hNgt⟩ := exists_nat_gt (2 / ε)
  have hNreal : (0 : ℝ) < N :=
    (div_pos (by norm_num) hε).trans hNgt
  have hN : 0 < N := by exact_mod_cast hNreal
  have hmesh : 2 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hNreal]
    have h := (div_lt_iff₀ hε).mp hNgt
    nlinarith
  let u (k : ℕ) : ℝ := (k : ℝ) / N
  have hu (k : ℕ) (hk : k ≤ N) : u k ∈ Icc (0 : ℝ) 1 := by
    dsimp [u]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hNreal.le
    · apply (div_le_one hNreal).mpr
      exact_mod_cast hk
  have hcenters (i : Fin N) : ∃ v : I, ball (u i.val) ε ⊆ W v := by
    apply hwindow
    exact hu i.val i.isLt.le
  choose vsel hvsel using hcenters
  have hone : 1 / (N : ℝ) < ε := by
    have hp : (0 : ℝ) < 1 / (N : ℝ) := one_div_pos.mpr hNreal
    have htwice : (2 : ℝ) / N = 2 * (1 / (N : ℝ)) := by ring
    rw [htwice] at hmesh
    nlinarith [hmesh]
  have hstep (k : ℕ) (hk : k < N) :
      ∃ B : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => B p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (B p.1).symm p.2) ∧
        ∃ S : Set (ℝ × ℝ), IsCompact S ∧
          (∀ t x, x ∉ S → B t x = x ∧ (B t).symm x = x) ∧
          (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, B t x = x ∧ (B t).symm x = x) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            range (fun y : ℝ => B t (D ((t, u k), y))) =
              range (fun y : ℝ => D ((t, u (k + 1)), y)) := by
    let i : Fin N := ⟨k, hk⟩
    have hui : u k ∈ ball (u i.val) ε := by
      simp only [i]
      simpa only [mem_ball, dist_self] using hε
    have hdiff : u (k + 1) - u k = 1 / (N : ℝ) := by
      dsimp [u]
      push_cast
      ring
    have huip : u (k + 1) ∈ ball (u i.val) ε := by
      rw [mem_ball, Real.dist_eq, hdiff, abs_of_pos (one_div_pos.mpr hNreal)]
      exact hone
    have hwi : u k ∈ W (vsel i) := hvsel i hui
    have hwip : u (k + 1) ∈ W (vsel i) := hvsel i huip
    have hwi' : u k ∈ Icc ((vsel i).1 - r (vsel i)) ((vsel i).1 + r (vsel i)) :=
      ⟨le_of_lt hwi.1, le_of_lt hwi.2⟩
    have hwip' : u (k + 1) ∈ Icc ((vsel i).1 - r (vsel i))
        ((vsel i).1 + r (vsel i)) :=
      ⟨le_of_lt hwip.1, le_of_lt hwip.2⟩
    let B : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) := fun t =>
      (A (vsel i) (t, u k)).symm.trans (A (vsel i) (t, u (k + 1)))
    have hcur : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
        A (vsel i) (p.1, u k) p.2) :=
      (hA (vsel i)).comp
        (((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
    have hcuri : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
        (A (vsel i) (p.1, u k)).symm p.2) :=
      (hAi (vsel i)).comp
        (((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
    have hnext : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
        A (vsel i) (p.1, u (k + 1)) p.2) :=
      (hA (vsel i)).comp
        (((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
    have hnexti : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
        (A (vsel i) (p.1, u (k + 1))).symm p.2) :=
      (hAi (vsel i)).comp
        (((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
    have hB : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => B p.1 p.2) :=
      hnext.comp (contDiff_fst.prodMk hcuri)
    have hBi : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (B p.1).symm p.2) :=
      hcur.comp (contDiff_fst.prodMk hnexti)
    refine ⟨B, hB, hBi, Q (vsel i), hQ (vsel i), ?_, ?_, ?_⟩
    · intro t x hx
      change A (vsel i) (t, u (k + 1))
          ((A (vsel i) (t, u k)).symm x) = x ∧
        A (vsel i) (t, u k)
          ((A (vsel i) (t, u (k + 1))).symm x) = x
      rw [(hfix (vsel i) (t, u k) x hx).2,
        (hfix (vsel i) (t, u (k + 1)) x hx).1,
        (hfix (vsel i) (t, u (k + 1)) x hx).2,
        (hfix (vsel i) (t, u k) x hx).1]
      exact ⟨rfl, rfl⟩
    · intro t ht x
      have hline (s : ℝ) (y : ℝ) :
          D ((t, s), y) = D ((t, (vsel i).1), y) := by
        rw [hstat t s y ht, hstat t (vsel i).1 y ht]
      have hleft := hstatA (vsel i) (t, u k) (hline (u k)) x
      have hright := hstatA (vsel i) (t, u (k + 1)) (hline (u (k + 1))) x
      change A (vsel i) (t, u (k + 1))
          ((A (vsel i) (t, u k)).symm x) = x ∧
        A (vsel i) (t, u k)
          ((A (vsel i) (t, u (k + 1))).symm x) = x
      rw [hleft.2, hright.1, hright.2, hleft.1]
      exact ⟨rfl, rfl⟩
    · intro t ht
      have hbase : u k ∈ Icc ((vsel i).1 - r (vsel i))
          ((vsel i).1 + r (vsel i)) := hwi'
      have hnextbase : u (k + 1) ∈ Icc ((vsel i).1 - r (vsel i))
          ((vsel i).1 + r (vsel i)) := hwip'
      have hcurRange := hArange (vsel i) t ht (u k) hbase
      have hnextRange := hArange (vsel i) t ht (u (k + 1)) hnextbase
      have hinv : (A (vsel i) (t, u k)).symm ''
          range (fun y : ℝ => D ((t, u k), y)) =
          range (fun y : ℝ => D ((t, (vsel i).1), y)) := by
        rw [← hcurRange, ← range_comp']
        simp only [Diffeomorph.symm_apply_apply]
      dsimp [B]
      rw [range_comp']
      rw [range_comp']
      change (A (vsel i) (t, u (k + 1))) ''
          ((A (vsel i) (t, u k)).symm ''
            range (fun y : ℝ => D ((t, u k), y))) = _
      rw [hinv]
      rw [← range_comp']
      exact hnextRange
  have hind (k : ℕ) (hk : k ≤ N) :
      ∃ G : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (G p.1).symm p.2) ∧
        ∃ S : Set (ℝ × ℝ), IsCompact S ∧
          (∀ t x, x ∉ S → G t x = x ∧ (G t).symm x = x) ∧
          (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, G t x = x ∧ (G t).symm x = x) ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            range (fun y : ℝ => G t (D ((t, 0), y))) =
              range (fun y : ℝ => D ((t, u k), y)) := by
    induction k with
    | zero =>
        let E : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) := fun _ =>
          Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞
        refine ⟨E, contDiff_snd, contDiff_snd, ∅, isCompact_empty, ?_, ?_, ?_⟩
        · intro t x hx
          exact ⟨rfl, rfl⟩
        · intro t ht x
          exact ⟨rfl, rfl⟩
        · intro t ht
          simp only [E, u, Nat.cast_zero, zero_div, Diffeomorph.coe_refl, id_eq]
    | succ k ih =>
        obtain ⟨G, hG, hGi, S, hS, hfixG, htailG, hRangeG⟩ :=
          ih (by omega)
        have hklt : k < N := Nat.lt_of_succ_le hk
        obtain ⟨B, hB, hBi, Q', hQ', hfixB, htailB, hRangeB⟩ := hstep k hklt
        let H : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) := fun t => (G t).trans (B t)
        refine ⟨H, hB.comp (contDiff_fst.prodMk hG),
          hGi.comp (contDiff_fst.prodMk hBi), S ∪ Q', hS.union hQ', ?_, ?_, ?_⟩
        · intro t x hx
          have hxS : x ∉ S := fun h => hx (Or.inl h)
          have hxQ : x ∉ Q' := fun h => hx (Or.inr h)
          change B t (G t x) = x ∧ (G t).symm ((B t).symm x) = x
          rw [(hfixG t x hxS).1, (hfixB t x hxQ).1,
            (hfixB t x hxQ).2, (hfixG t x hxS).2]
          exact ⟨rfl, rfl⟩
        · intro t ht x
          change B t (G t x) = x ∧ (G t).symm ((B t).symm x) = x
          rw [(htailG t ht x).1, (htailB t ht x).1,
            (htailB t ht x).2, (htailG t ht x).2]
          exact ⟨rfl, rfl⟩
        · intro t ht
          change range (fun y : ℝ => B t (G t (D ((t, 0), y)))) = _
          rw [range_comp', hRangeG t ht]
          rw [← range_comp']
          exact hRangeB t ht
  obtain ⟨G, hG, hGi, S, hS, hfixG, htailG, hRangeG⟩ := hind N le_rfl
  refine ⟨G, hG, hGi, ⟨S, hS, hfixG⟩, htailG, ?_⟩
  intro t ht
  simpa only [u, div_self (ne_of_gt hNreal)] using hRangeG t ht

end PoincareConjecture.M25.Topology3D
