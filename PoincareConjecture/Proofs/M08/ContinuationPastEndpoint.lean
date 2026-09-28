import PoincareConjecture.Proofs.M08.ContinuationCurve
import PoincareConjecture.Proofs.M08.ContinuationEndpoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1400000 in
theorem exists_continuation_past_positive_endpoint {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    {a d b : ℝ} (ha : 0 < a) (had : a < d) (hdb : d < b)
    (htime : ∀ s ∈ Ioo 0 b, T - s ^ 2 ∈ interior J)
    (α β : ℝ → M) (hα : IsContinuationCurve F T α (Ioo a b))
    (hβα : EqOn β α (Ioi a)) (x : M)
    (hsrc : MapsTo β (Icc a d) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Pbar : ℝ → EuclideanSpace ℝ (Fin n))
    (hphase : ∀ s ∈ Icc a d, HasDerivWithinAt
      (fun r ↦ (extChartAt (𝓡 n) x (β r), Pbar r))
      (closedChartEulerPhase F T x (Icc a d) s (extChartAt (𝓡 n) x (β s), Pbar s))
      (Icc a d) s) :
    ∃ e : ℝ, 0 ≤ e ∧ e < a ∧ ∃ δ : ℝ → M,
      IsContinuationCurve F T δ (Ioo e b) ∧ EqOn δ α (Ioo a b) := by
  classical
  let chart := extChartAt (𝓡 n) x
  let z := fun r ↦ (chart (β r), Pbar r)
  have hab : a < b := had.trans hdb
  have haC : a ∈ Icc a d := ⟨le_rfl, had.le⟩
  have htarget (r : ℝ) (hr : r ∈ Icc a d) : chart (β r) ∈ chart.target := by
    apply chart.map_source
    simpa only [chart, extChartAt_source] using hsrc hr
  obtain ⟨ε, hε, γ, hWU, hγ, hγ₀, hγsrc⟩ :=
    exists_continuationCurve_from_phase F hM04 T x isOpen_Ioo htime
      (show a ∈ Ioo 0 b from ⟨ha, hab⟩) (chart (β a)) (Pbar a) (htarget a haC)
  let W := Ioo (a - 2 * ε) (a + 2 * ε)
  have haW : a ∈ W := ⟨by linarith, by linarith⟩
  have htimeC (r : ℝ) (hr : r ∈ Icc a d) : T - r ^ 2 ∈ J :=
    interior_subset (htime r ⟨ha.trans_le hr.1, hr.2.trans_lt hdb⟩)
  obtain ⟨k₀, hak₀, hk₀m⟩ := exists_between (lt_min had (show a < a + ε by linarith))
  have hk₀d : k₀ < d := hk₀m.trans_le (min_le_left d (a + ε))
  have hsmall : Icc a k₀ ⊆ Icc a d := Icc_subset_Icc_right hk₀d.le
  have hsmallW : Icc a k₀ ⊆ W := by
    intro r hr
    have hk₀ε := hk₀m.trans_le (min_le_right d (a + ε))
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let f := closedChartEulerPhase F T x univ
  let w := continuationCurvePhase F T x γ
  have hz (r : ℝ) (hr : r ∈ Icc a k₀) :
      HasDerivWithinAt z (f r (z r)) (Icc a k₀) r := by
    have h := (hphase r (hsmall hr)).mono hsmall
    rw [closedChartEulerPhase_eq_univ F hM04 T x htimeC (hsmall hr)
      (htime r ⟨ha.trans_le hr.1, (hr.2.trans hk₀d.le).trans_lt hdb⟩)
      _ (htarget r (hsmall hr))] at h
    exact h
  have hw (r : ℝ) (hr : r ∈ Icc a k₀) :
      HasDerivWithinAt w (f r (w r)) (Icc a k₀) r :=
    (hγ.phase r (hsmallW hr) x (hγsrc (hsmallW hr))).hasDerivWithinAt
  have hdom : (a, z a) ∈ Ioo 0 b ×ˢ (chart.target ×ˢ univ) :=
    ⟨⟨ha, hab⟩, htarget a haC, mem_univ _⟩
  have hf : ContDiffAt ℝ 1 (Function.uncurry f) (a, z a) :=
    (((continuationChartPhase_contDiffOn F hM04 T x isOpen_Ioo
      (fun r hr ↦ interior_subset (htime r hr))) _ hdom).contDiffAt
      ((isOpen_Ioo.prod ((isOpen_extChartAt_target (I := 𝓡 n) x).prod isOpen_univ)).mem_nhds
        hdom)).of_le (by simp)
  obtain ⟨k, hak, hkk₀, hzw⟩ := smooth_phase_eqOn_right f hak₀ hf hz hw hγ₀.symm
  have hkg (r : ℝ) (hr : r ∈ Icc a k) : β r = γ r := by
    have hr₀ : r ∈ Icc a k₀ := ⟨hr.1, hr.2.trans hkk₀.le⟩
    have heq : chart (β r) = chart (γ r) := congrArg Prod.fst (hzw hr)
    have hβsrc : β r ∈ chart.source := by
      simpa only [chart, extChartAt_source] using hsrc (hsmall hr₀)
    have hγsrc' : γ r ∈ chart.source := by
      simpa only [chart, extChartAt_source] using hγsrc (hsmallW hr₀)
    exact (chart.left_inv hβsrc).symm.trans
      ((congrArg chart.symm heq).trans (chart.left_inv hγsrc'))
  let e := a - ε
  have heW : e ∈ W := ⟨by dsimp only [e, W]; linarith, by dsimp only [e, W]; linarith⟩
  have he : 0 ≤ e := (hWU heW).1.le
  have hea : e < a := by dsimp only [e]; linarith
  let δ := fun r ↦ if r ≤ a then γ r else α r
  have hδα : EqOn δ α (Ioo a b) := by
    intro r hr
    simp only [δ, if_neg hr.1.not_ge]
  have hδγ : EqOn δ γ (Ioo e k) := by
    intro r hr
    dsimp only [δ]
    split_ifs with hra
    · rfl
    · exact (hβα (lt_of_not_ge hra)).symm.trans
        (hkg r ⟨(lt_of_not_ge hra).le, hr.2.le⟩)
  have hekW : Ioo e k ⊆ W := by
    intro r hr
    have hkε := hkk₀.trans (hk₀m.trans_le (min_le_right d (a + ε)))
    exact ⟨by dsimp only [W, e] at *; linarith [hr.1],
      by linarith [hr.2]⟩
  have hδL := (hγ.mono hekW).congr isOpen_Ioo hδγ
  have hδR := hα.congr isOpen_Ioo hδα
  refine ⟨e, he, hea, δ, (hδL.union isOpen_Ioo isOpen_Ioo hδR).mono ?_, hδα⟩
  intro r hr
  by_cases hrk : r < k
  · exact Or.inl ⟨hr.1, hrk⟩
  · exact Or.inr ⟨hak.trans_le (le_of_not_gt hrk), hr.2⟩

end PoincareConjecture.M08
