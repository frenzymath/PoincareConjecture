import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ObstacleBarriers
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseStripSeparation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem exists_axis_height_avoiding
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {s : ℝ}
    (hs : (s, (0 : ℝ)) ∈ F.source) {C : Set AnnulusCoordinates} (hC : IsClosed C)
    (havoid : F (s, 0) ∉ C) :
    ∃ delta > 0, ∀ z : ℝ, |z| < delta → F (s, z) ∉ C := by
  have hc : ContinuousAt (fun z : ℝ => F (s, z)) 0 :=
    (F.continuousAt hs).comp ((continuous_const.prodMk continuous_id).continuousAt)
  have hnear := hc.preimage_mem_nhds (hC.isOpen_compl.mem_nhds havoid)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨delta, hdelta, fun z hz => hball ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz

theorem m64Intrinsic_exists_obstacle_avoiding_strip_chain
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) (hinj : InjOn gamma (Icc a b))
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    (d : ℝ → AnnulusCoordinates)
    (hd : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t))
    {C : Set AnnulusCoordinates} (hC : IsClosed C)
    (havoid : ∀ t ∈ Ioo a b, gamma t ∉ C)
    (ellA ellB : AnnulusCoordinates →L[ℝ] ℝ)
    (hcutA : ellA (d a) = 0) (hcutB : ellB (d b) = 0)
    (htangentA : 0 < ellA (deriv gamma a)) (htangentB : ellB (deriv gamma b) < 0)
    {WA WB : Set AnnulusCoordinates} (hWA : IsOpen WA) (hWB : IsOpen WB)
    (haW : gamma a ∈ WA) (hbW : gamma b ∈ WB)
    (hsepA : ∀ z ∈ C ∩ WA, ellA (z - gamma a) ≤ 0)
    (hsepB : ∀ z ∈ C ∩ WB, ellB (z - gamma b) ≤ 0) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
      (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ)
      (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (G i).target)
      (P : ∀ i, TransverseGraphCuts (f i) (G i (c i.castSucc)) (G i (c i.succ))
        (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
        (L i (d (c i.succ))).1 (L i (d (c i.succ))).2),
      let F (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
      ∃ delta > 0, 0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
        (∀ i, Icc (c i.castSucc) (c i.succ) ⊆ (G i).source ∧
          StrictMonoOn (G i) (G i).source ∧ ContDiffOn ℝ ∞ (G i) (G i).source ∧
          (∀ t ∈ (G i).source, L i (gamma t) = (G i t, f i (G i t))) ∧
          G i '' Icc (c i.castSucc) (c i.succ) =
            Icc (G i (c i.castSucc)) (G i (c i.succ)) ∧
          Icc (G i (c i.castSucc)) (G i (c i.succ)) ⊆ (G i).target) ∧
        (∀ i, delta ≤ (P i).radius ∧
          Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ (F i).source ∧
          (fun t => F i (t, 0)) '' Icc (0 : ℝ) 1 =
            gamma '' Icc (c i.castSucc) (c i.succ)) ∧
        (∀ i j : Fin n, i.succ < j.castSucc →
          Disjoint (F i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta))
            (F j '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta))) ∧
        (∀ i j : Fin n, i.succ = j.castSucc →
          ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ z w : ℝ, |z| < delta → |w| < delta →
            F i (t, z) = F j (s, w) → t = 1 ∧ s = 0) ∧
        ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < delta → F i (t, z) ∈ C →
          (c i.castSucc = a ∧ t = 0) ∨ (c i.succ = b ∧ t = 1) := by
  classical
  obtain ⟨n, c, L, G, f, hf, P, rho, hrho, hn, hc, hfirst, hlast,
    hgraph, hstrip, hdisjoint, hadj⟩ :=
    m64Intrinsic_exists_separated_transverse_arc_strips hg hab hinj hregular d hd
  let F (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
  have hstep (i : Fin n) := hc (Fin.castSucc_lt_succ (i := i))
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hleft (i : Fin n) : ∃ (ell : AnnulusCoordinates →L[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsOpen W ∧ gamma (c i.castSucc) ∈ W ∧ ell (d (c i.castSucc)) = 0 ∧
      0 < ell (deriv gamma (c i.castSucc)) ∧
      ∀ z ∈ C ∩ W, ell (z - gamma (c i.castSucc)) ≤ 0 := by
    by_cases heq : c i.castSucc = a
    · exact ⟨ellA, WA, hWA, heq ▸ haW, by simpa only [heq] using hcutA,
        by simpa only [heq] using htangentA, by simpa only [heq] using hsepA⟩
    · have ht : c i.castSucc ∈ Ioo a b :=
        ⟨lt_of_le_of_ne (hcut i.castSucc).1 (Ne.symm heq),
          (hstep i).trans_le (hcut i.succ).2⟩
      exact m64Intrinsic_exists_internal_obstacle_barrier hC (havoid _ ht)
        (hd _ (hcut i.castSucc)) false
  have hright (i : Fin n) : ∃ (ell : AnnulusCoordinates →L[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsOpen W ∧ gamma (c i.succ) ∈ W ∧ ell (d (c i.succ)) = 0 ∧
      ell (deriv gamma (c i.succ)) < 0 ∧
      ∀ z ∈ C ∩ W, ell (z - gamma (c i.succ)) ≤ 0 := by
    by_cases heq : c i.succ = b
    · exact ⟨ellB, WB, hWB, heq ▸ hbW, by simpa only [heq] using hcutB,
        by simpa only [heq] using htangentB, by simpa only [heq] using hsepB⟩
    · have ht : c i.succ ∈ Ioo a b :=
        ⟨(hcut i.castSucc).1.trans_lt (hstep i), lt_of_le_of_ne (hcut i.succ).2 heq⟩
      exact m64Intrinsic_exists_internal_obstacle_barrier hC (havoid _ ht)
        (hd _ (hcut i.succ)) true
  choose ellL WL hWL hpL hkL htL hsL using hleft
  choose ellR WR hWR hpR hkR htR hsR using hright
  have hwidth (i : Fin n) := m64Intrinsic_exists_obstacle_avoiding_graph_strip hg
    (hstep i) (fun t ht => hregular t ⟨(hcut i.castSucc).1.trans ht.1,
      ht.2.trans (hcut i.succ).2⟩) (L i) (G i) (hgraph i).2.2.1 (hf i)
    (hgraph i).2.1 (hgraph i).1 (hgraph i).2.2.2.1 (hgraph i).2.2.2.2.1 hC
    (fun t ht => havoid t ⟨(hcut i.castSucc).1.trans_lt ht.1,
      ht.2.trans_le (hcut i.succ).2⟩) (d (c i.castSucc)) (d (c i.succ)) (P i)
    (ellL i) (ellR i) (hkL i) (hkR i) (htL i) (htR i)
    (hWL i) (hWR i) (hpL i) (hpR i) (hsL i) (hsR i)
  choose width hwidth hwP hwsource hwavoid using hwidth
  have hleftBase (i : Fin n) : F i (0, 0) = gamma (c i.castSucc) := by
    rw [(P i).linearCoordinates_axis]
    simp only [zero_mul, add_zero]
    rw [← (hgraph i).2.2.2.1 _ ((hgraph i).1 (left_mem_Icc.mpr (hstep i).le)),
      (L i).symm_apply_apply]
  have hrightBase (i : Fin n) : F i (1, 0) = gamma (c i.succ) := by
    rw [(P i).linearCoordinates_axis]
    simp only [one_mul, add_sub_cancel]
    rw [← (hgraph i).2.2.2.1 _ ((hgraph i).1 (right_mem_Icc.mpr (hstep i).le)),
      (L i).symm_apply_apply]
  have hleftTube (i : Fin n) : ∃ epsilon > 0,
      c i.castSucc ≠ a → ∀ z : ℝ, |z| < epsilon → F i (0, z) ∉ C := by
    by_cases heq : c i.castSucc = a
    · exact ⟨1, zero_lt_one, fun hne => (hne heq).elim⟩
    · have ht : c i.castSucc ∈ Ioo a b :=
        ⟨lt_of_le_of_ne (hcut i.castSucc).1 (Ne.symm heq),
          (hstep i).trans_le (hcut i.succ).2⟩
      obtain ⟨epsilon, hepsilon, havoid'⟩ := exists_axis_height_avoiding (F i)
        (hwsource i 0 (by simp) 0 (by simpa only [abs_zero] using hwidth i)) hC
        (hleftBase i ▸ havoid _ ht)
      exact ⟨epsilon, hepsilon, fun _ => havoid'⟩
  have hrightTube (i : Fin n) : ∃ epsilon > 0,
      c i.succ ≠ b → ∀ z : ℝ, |z| < epsilon → F i (1, z) ∉ C := by
    by_cases heq : c i.succ = b
    · exact ⟨1, zero_lt_one, fun hne => (hne heq).elim⟩
    · have ht : c i.succ ∈ Ioo a b :=
        ⟨(hcut i.castSucc).1.trans_lt (hstep i), lt_of_le_of_ne (hcut i.succ).2 heq⟩
      obtain ⟨epsilon, hepsilon, havoid'⟩ := exists_axis_height_avoiding (F i)
        (hwsource i 1 (by simp) 0 (by simpa only [abs_zero] using hwidth i)) hC
        (hrightBase i ▸ havoid _ ht)
      exact ⟨epsilon, hepsilon, fun _ => havoid'⟩
  choose leftRadius hlRadius hlAvoid using hleftTube
  choose rightRadius hrRadius hrAvoid using hrightTube
  obtain ⟨eta, heta, hle⟩ := exists_pos_le_finite_family
    (fun i => min (width i) (min (leftRadius i) (rightRadius i)))
    (fun i => lt_min (hwidth i) (lt_min (hlRadius i) (hrRadius i)))
  let delta := min rho eta
  have hdelta : 0 < delta := lt_min hrho heta
  have hdR : delta ≤ rho := min_le_left _ _
  have hdw (i : Fin n) : delta ≤ width i :=
    (min_le_right _ _).trans ((hle i).trans (min_le_left _ _))
  have hdl (i : Fin n) : delta ≤ leftRadius i :=
    (min_le_right _ _).trans ((hle i).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdr (i : Fin n) : delta ≤ rightRadius i :=
    (min_le_right _ _).trans ((hle i).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsub : Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ Icc (0 : ℝ) 1 ×ˢ Ioo (-rho) rho :=
    prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg hdR) hdR)
  refine ⟨n, c, L, G, f, hf, P, delta, hdelta, hn, hc, hfirst, hlast, hgraph,
    fun i => ⟨hdR.trans (hstrip i).1, hsub.trans (hstrip i).2.1, (hstrip i).2.2⟩,
    fun i j hij => (hdisjoint i j hij).mono (image_mono hsub) (image_mono hsub),
    fun i j hij t ht s hs z w hz hw => hadj i j hij t ht s hs z w
      (hz.trans_le hdR) (hw.trans_le hdR), ?_⟩
  intro i t ht z hz hmem
  by_cases ht0 : t = 0
  · subst t
    refine Or.inl ⟨?_, rfl⟩
    by_contra hne
    exact hlAvoid i hne z (hz.trans_le (hdl i)) hmem
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have ht1 : t = 1 := by
      by_contra hne
      exact hwavoid i t ⟨htpos, lt_of_le_of_ne ht.2 hne⟩ z (hz.trans_le (hdw i)) hmem
    subst t
    refine Or.inr ⟨?_, rfl⟩
    by_contra hne
    exact hrAvoid i hne z (hz.trans_le (hdr i)) hmem

end PoincareConjecture
