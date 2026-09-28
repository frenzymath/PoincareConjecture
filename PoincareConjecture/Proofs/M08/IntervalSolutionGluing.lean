import PoincareConjecture.Proofs.M08.OverlappingIntervals

set_option autoImplicit false

open Set Filter Topology

namespace PoincareConjecture.M08

theorem lt_of_Icc_mem_nhdsWithin_Icc {a b l r s : ℝ} (hab : a < b)
    (hs : s ∈ Icc a b) (hnear : Icc l r ∈ 𝓝[Icc a b] s) : l < r := by
  obtain ⟨U, hU, hsU, hsub⟩ := mem_nhdsWithin.mp hnear
  obtain ⟨u, v, ⟨hus, hsv⟩, huv⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hsU)
  let p := max a ((u + s) / 2)
  let q := min b ((s + v) / 2)
  have hups : u < (u + s) / 2 ∧ (u + s) / 2 < s := by constructor <;> linarith
  have hsqv : s < (s + v) / 2 ∧ (s + v) / 2 < v := by constructor <;> linarith
  have hpq : p < q := max_lt
    (lt_min hab (hs.1.trans_lt hsqv.1))
    (lt_min (hups.2.trans_le hs.2) (hups.2.trans hsqv.1))
  have hps : p ≤ s := max_le hs.1 hups.2.le
  have hsq : s ≤ q := le_min hs.2 hsqv.1.le
  have hp : p ∈ Icc l r := hsub ⟨huv ⟨hups.1.trans_le (le_max_right _ _),
    hps.trans_lt hsv⟩, ⟨le_max_left _ _, hps.trans hs.2⟩⟩
  have hq : q ∈ Icc l r := hsub ⟨huv ⟨hus.trans_le hsq,
    (min_le_right _ _).trans_lt hsqv.2⟩, ⟨hs.1.trans hsq, min_le_left _ _⟩⟩
  exact (hp.1.trans_lt hpq).trans_le hq.2

structure IntervalSolutionLocality {X : Type*}
    (Sol : ℝ → ℝ → (ℝ → X) → Prop) : Prop where
  restrict : ∀ {a b c d : ℝ} {f : ℝ → X},
    a ≤ c → c < d → d ≤ b → Sol a b f → Sol c d f
  paste : ∀ {a l c r : ℝ} {f g : ℝ → X},
    a ≤ l → l < c → c < r → Sol a c f → Sol l r g → EqOn f g (Icc l c) →
      Sol a r (fun s ↦ if s ≤ c then f s else g s)

set_option maxHeartbeats 1000000 in
theorem exists_interval_solution_of_overlapping_cover {X : Type*}
    (Sol : ℝ → ℝ → (ℝ → X) → Prop) (hSol : IntervalSolutionLocality Sol)
    {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (t : Fin (m + 1) → ℝ) (l r : Fin m → ℝ)
    (ht : Monotone t) (hta : t 0 = a) (htb : t (Fin.last m) = b)
    (hpieces : ∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧ l i ≤ t i.castSucc ∧
      t i.succ ≤ r i ∧ ∀ s ∈ Icc (t i.castSucc) (t i.succ),
        Icc (l i) (r i) ∈ 𝓝[Icc a b] s)
    (hlocal : ∀ i s, s ∈ Icc (l i) (r i) → ∀ z : X,
      ∃ f : ℝ → X, Sol (l i) (r i) f ∧ f s = z)
    (hunique : ∀ i {c d : ℝ}, l i ≤ c → c < d → d ≤ r i →
      ∀ {f g : ℝ → X}, Sol c d f → Sol c d g →
        ∀ s ∈ Icc c d, f s = g s → EqOn f g (Icc c d))
    (z₀ : X) : ∃ f : ℝ → X, Sol a b f ∧ f a = z₀ := by
  classical
  have hstep : ∀ k (hk : k < m), ∃ c : ℝ, ∃ f : ℝ → X,
      a < c ∧ c ≤ b ∧ t ⟨k + 1, Nat.succ_lt_succ hk⟩ ≤ c ∧
        Icc a c ∈ 𝓝[Icc a b] (t ⟨k + 1, Nat.succ_lt_succ hk⟩) ∧
          Sol a c f ∧ f a = z₀ := by
    intro k
    induction k with
    | zero =>
      intro hk
      let i : Fin m := ⟨0, hk⟩
      obtain ⟨hal, hlr, hrb, hlt, htr, hnear⟩ := hpieces i
      have hzero : t i.castSucc = a := hta
      have hla : l i = a := le_antisymm (hzero ▸ hlt) hal
      have ha : a ∈ Icc (l i) (r i) := ⟨hla.le, hla ▸ hlr.le⟩
      obtain ⟨f, hf, hf0⟩ := hlocal i a ha z₀
      have hnext := hnear (t i.succ) ⟨ht (show i.castSucc ≤ i.succ from Nat.le_succ i.val), le_rfl⟩
      refine ⟨r i, f, hla ▸ hlr, hrb, htr, ?_, ?_, hf0⟩
      · change Icc a (r i) ∈ 𝓝[Icc a b] (t i.succ)
        simpa only [hla] using hnext
      · simpa only [hla] using hf
    | succ k ih =>
      intro hk
      have hk' : k < m := (Nat.lt_succ_self k).trans hk
      obtain ⟨c, f, hac, hcb, htc, hprefix, hf, hf0⟩ := ih hk'
      let i : Fin m := ⟨k + 1, hk⟩
      obtain ⟨hal, hlr, hrb, hlt, htr, hnear⟩ := hpieces i
      have hcore : t i.castSucc ≤ t i.succ :=
        ht (show i.castSucc ≤ i.succ from Nat.le_succ i.val)
      have hstart : t i.castSucc ∈ Icc (l i) (r i) := ⟨hlt, hcore.trans htr⟩
      have hstartC : t i.castSucc ∈ Icc a b :=
        ⟨hal.trans hlt, (hcore.trans htr).trans hrb⟩
      have hprefix' : Icc a c ∈ 𝓝[Icc a b] (t i.castSucc) := hprefix
      have hover : Icc (l i) (min c (r i)) ∈ 𝓝[Icc a b] (t i.castSucc) := by
        apply mem_of_superset (inter_mem hprefix' (hnear _ ⟨le_rfl, hcore⟩))
        intro s hs
        exact ⟨hs.2.1, le_min hs.1.2 hs.2.2⟩
      have hlmin := lt_of_Icc_mem_nhdsWithin_Icc hab hstartC hover
      obtain ⟨g, hg, hgf⟩ := hlocal i (t i.castSucc) hstart (f (t i.castSucc))
      have heq : EqOn f g (Icc (l i) (min c (r i))) := by
        apply hunique i le_rfl hlmin (min_le_right _ _)
          (hSol.restrict hal hlmin (min_le_left _ _) hf)
          (hSol.restrict le_rfl hlmin (min_le_right _ _) hg) (t i.castSucc)
          ⟨hlt, le_min htc hstart.2⟩ hgf.symm
      have hnext := hnear (t i.succ) ⟨hcore, le_rfl⟩
      by_cases hrc : r i ≤ c
      · refine ⟨c, f, hac, hcb, htr.trans hrc, ?_, hf, hf0⟩
        exact mem_of_superset hnext (Icc_subset_Icc hal hrc)
      · have hcr : c < r i := lt_of_not_ge hrc
        have hlc : l i < c := hlmin.trans_le (min_le_left _ _)
        have heq' : EqOn f g (Icc (l i) c) := by
          simpa only [min_eq_left hcr.le] using heq
        refine ⟨r i, (fun s ↦ if s ≤ c then f s else g s),
          hac.trans hcr, hrb, htr, ?_, hSol.paste hal hlc hcr hf hg heq', ?_⟩
        · exact mem_of_superset hnext (Icc_subset_Icc hal le_rfl)
        · simpa only [if_pos hac.le] using hf0
  have hk : m - 1 < m := by omega
  obtain ⟨c, f, hac, hcb, htc, hnear, hf, hf0⟩ := hstep (m - 1) hk
  have hlast : (⟨m - 1 + 1, Nat.succ_lt_succ hk⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  have hbc : b ≤ c := by simpa only [hlast, htb] using htc
  have hceq : c = b := le_antisymm hcb hbc
  exact ⟨f, hceq ▸ hf, hf0⟩

end PoincareConjecture.M08
