import PoincareConjecture.Proofs.M04.ShiParallelFrames

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle NNReal

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_shi_segmented_parallel_frames [T2Space M]
    (D : LeviCivitaData g) {N : ℕ} (hN : 0 < N)
    (s : ℕ → ℝ) (hs : ∀ j < N, s j < s (j + 1))
    (c : Fin N → OpenPartialHomeomorph M E)
    (hc : ∀ j, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c j) (c j).source)
    (hi : ∀ j, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c j).symm (c j).target)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : ∀ j : Fin N,
      MapsTo γ (Icc (s j.val) (s (j.val + 1))) (c j).source)
    (K : Fin N → ℝ≥0)
    (hK : ∀ j : Fin N, ∀ t ∈ Icc (s j.val) (s (j.val + 1)),
      ‖shiChartChristoffel D (c j) (c j (γ t))
        (deriv ((c j) ∘ γ) t)‖ ≤ (K j : ℝ))
    (hshort : ∀ j : Fin N,
      s (j.val + 1) - s j.val ≤ 1 / (2 * (K j : ℝ) + 1))
    (Jend : E →L[ℝ] TangentSpace (𝓡 n) (γ (s N))) :
    ∃ P : Fin N → ℝ → E →L[ℝ] E,
      (∀ j, ContDiffOn ℝ 1 (P j) (Icc (s j.val) (s (j.val + 1)))) ∧
      (∀ j t, t ∈ Icc (s j.val) (s (j.val + 1)) →
        HasDerivWithinAt (P j)
          (-((shiChartChristoffel D (c j) (c j (γ t))
            (deriv ((c j) ∘ γ) t)).comp (P j t)))
          (Icc (s j.val) (s (j.val + 1))) t) ∧
      (∀ (j : ℕ) (hj : j + 1 < N) (v : E),
        shiChartField (c ⟨j, (Nat.lt_succ_self j).trans hj⟩)
            (P ⟨j, (Nat.lt_succ_self j).trans hj⟩ (s (j + 1)) v)
            (γ (s (j + 1))) =
          shiChartField (c ⟨j + 1, hj⟩)
            (P ⟨j + 1, hj⟩ (s (j + 1)) v) (γ (s (j + 1)))) ∧
      (∀ (j : Fin N), j.val + 1 = N → ∀ v,
        shiChartField (c j) (P j (s N) v) (γ (s N)) = Jend v) ∧
      ∀ (j : Fin N) t, t ∈ Icc (s j.val) (s (j.val + 1)) → ∀ v w,
        g.inner (γ t) (shiChartField (c j) (P j t v) (γ t))
          (shiChartField (c j) (P j t w) (γ t)) =
        g.inner (γ (s N)) (Jend v) (Jend w) := by
  classical
  let Suffix (k : ℕ) : Prop :=
    ∃ P : Fin N → ℝ → E →L[ℝ] E,
      (∀ j, k ≤ j.val →
        ContDiffOn ℝ 1 (P j) (Icc (s j.val) (s (j.val + 1)))) ∧
      (∀ j, k ≤ j.val → ∀ t, t ∈ Icc (s j.val) (s (j.val + 1)) →
        HasDerivWithinAt (P j)
          (-((shiChartChristoffel D (c j) (c j (γ t))
            (deriv ((c j) ∘ γ) t)).comp (P j t)))
          (Icc (s j.val) (s (j.val + 1))) t) ∧
      (∀ (j : ℕ) (hj : j + 1 < N), k ≤ j → ∀ v,
        shiChartField (c ⟨j, (Nat.lt_succ_self j).trans hj⟩)
            (P ⟨j, (Nat.lt_succ_self j).trans hj⟩ (s (j + 1)) v)
            (γ (s (j + 1))) =
          shiChartField (c ⟨j + 1, hj⟩)
            (P ⟨j + 1, hj⟩ (s (j + 1)) v) (γ (s (j + 1)))) ∧
      (∀ j, k ≤ j.val → j.val + 1 = N → ∀ v,
        shiChartField (c j) (P j (s N) v) (γ (s N)) = Jend v) ∧
      ∀ j, k ≤ j.val → ∀ t, t ∈ Icc (s j.val) (s (j.val + 1)) → ∀ v w,
        g.inner (γ t) (shiChartField (c j) (P j t v) (γ t))
          (shiChartField (c j) (P j t w) (γ t)) =
        g.inner (γ (s N)) (Jend v) (Jend w)
  have hbase : Suffix N := by
    refine ⟨fun _ _ => 0, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      exact False.elim ((not_le_of_gt j.isLt) hj)
    · intro j hj
      exact False.elim ((not_le_of_gt j.isLt) hj)
    · intro j hj hNj
      omega
    · intro j hj
      exact False.elim ((not_le_of_gt j.isLt) hj)
    · intro j hj
      exact False.elim ((not_le_of_gt j.isLt) hj)
  have hstep : ∀ k < N, 0 ≤ k → Suffix (k + 1) → Suffix k := by
    intro k hk _ htail
    obtain ⟨P, hP, hPd, hPjoin, hPend, hPpair⟩ := htail
    let i : Fin N := ⟨k, hk⟩
    let J : E →L[ℝ] TangentSpace (𝓡 n) (γ (s (k + 1))) :=
      if hnext : k + 1 < N then
        (mvfderiv (𝓡 n) (c ⟨k + 1, hnext⟩) (γ (s (k + 1)))).inverse.comp
          (P ⟨k + 1, hnext⟩ (s (k + 1)))
      else Jend
    have hJnext (hnext : k + 1 < N) (v : E) :
        J v = shiChartField (c ⟨k + 1, hnext⟩)
          (P ⟨k + 1, hnext⟩ (s (k + 1)) v) (γ (s (k + 1))) := by
      simp only [J, dif_pos hnext]
      rfl
    have hJend (hlast : k + 1 = N) (v : E) : J v = Jend v := by
      simp only [J, dif_neg (show ¬k + 1 < N by omega)]
      rfl
    have hJpair (v w : E) :
        g.inner (γ (s (k + 1))) (J v) (J w) =
          g.inner (γ (s N)) (Jend v) (Jend w) := by
      by_cases hnext : k + 1 < N
      · rw [hJnext hnext, hJnext hnext]
        exact hPpair ⟨k + 1, hnext⟩ le_rfl (s (k + 1))
          ⟨le_rfl, (hs (k + 1) hnext).le⟩ v w
      · have hlast : k + 1 = N := by omega
        rw [hJend hlast, hJend hlast]
        exact congrArg (fun z => g.inner (γ (s z)) (Jend v) (Jend w)) hlast
    obtain ⟨F, hF, hFd, hFend, hFpair⟩ :=
      exists_shiChart_native_parallel_frame D (hc i) (hi i) (hs k hk) hγ
        (hinside i) (K i) (hK i) (hshort i) J
    let Pnew : Fin N → ℝ → E →L[ℝ] E :=
      fun j => if j.val = k then F else P j
    refine ⟨Pnew, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hjk : j.val = k
      · have he : j = i := Fin.ext hjk
        subst j
        simpa only [Pnew, i, ite_true] using hF
      · have hj' : k + 1 ≤ j.val := by omega
        simpa only [Pnew, if_neg hjk] using hP j hj'
    · intro j hj t ht
      by_cases hjk : j.val = k
      · have he : j = i := Fin.ext hjk
        subst j
        simpa only [Pnew, i, ite_true] using hFd t ht
      · have hj' : k + 1 ≤ j.val := by omega
        simpa only [Pnew, if_neg hjk] using hPd j hj' t ht
    · intro j hj hkj v
      have hnextne : j + 1 ≠ k := by omega
      by_cases hjk : j = k
      · subst j
        simpa only [Pnew, ite_true, if_neg hnextne, i] using
          (hFend v).trans (hJnext hj v)
      · have hj' : k + 1 ≤ j := by omega
        simpa only [Pnew, if_neg hjk, if_neg hnextne] using hPjoin j hj hj' v
    · intro j hj hjlast v
      by_cases hjk : j.val = k
      · have he : j = i := Fin.ext hjk
        subst j
        have hlast : k + 1 = N := hjlast
        have hend := (hFend v).trans (hJend hlast v)
        have htime := congrArg (fun r : ℝ =>
          (shiChartField (c i) (F r v) (γ r) : E)) (congrArg s hlast.symm)
        simpa only [Pnew, i, ite_true] using! htime.trans hend
      · have hj' : k + 1 ≤ j.val := by omega
        simpa only [Pnew, if_neg hjk] using hPend j hj' hjlast v
    · intro j hj t ht v w
      by_cases hjk : j.val = k
      · have he : j = i := Fin.ext hjk
        subst j
        simpa only [Pnew, i, ite_true] using!
          (hFpair t ht v w).trans (hJpair v w)
      · have hj' : k + 1 ≤ j.val := by omega
        simpa only [Pnew, if_neg hjk] using hPpair j hj' t ht v w
  have hzero : Suffix 0 := Nat.decreasingInduction' hstep (Nat.zero_le N) hbase
  obtain ⟨P, hP, hPd, hPjoin, hPend, hPpair⟩ := hzero
  exact ⟨P, fun j => hP j (Nat.zero_le _),
    fun j => hPd j (Nat.zero_le _), fun j hj => hPjoin j hj (Nat.zero_le _),
    fun j => hPend j (Nat.zero_le _), fun j => hPpair j (Nat.zero_le _)⟩

end PoincareConjecture.M04
