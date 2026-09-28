import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InwardLoopOrientation













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture





theorem m64Intrinsic_exists_inward_separated_arc_strips
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a < b) (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (g : ℝ → AnnulusCoordinates) (l u : ℝ)
      (n : ℕ) (c : Fin (n + 1) → ℝ)
      (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ)
      (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (G i).target)
      (P : ∀ i, TransverseGraphCuts (f i) (G i (c i.castSucc)) (G i (c i.succ))
        (L i (quarterTurn (deriv g (c i.castSucc)))).1
        (L i (quarterTurn (deriv g (c i.castSucc)))).2
        (L i (quarterTurn (deriv g (c i.succ)))).1
        (L i (quarterTurn (deriv g (c i.succ)))).2),
      let F (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
      (g = gamma ∨ g = fun t => gamma (T - t)) ∧
      ContDiff ℝ ∞ g ∧ g 0 = g T ∧ InjOn g (Ico 0 T) ∧
      g '' Icc 0 T = gamma '' Icc 0 T ∧ 0 < l ∧ l < u ∧ u < T ∧
      ∃ delta > 0, 0 < n ∧ StrictMono c ∧ c 0 = l ∧ c (Fin.last n) = u ∧
        (∀ i, Icc (c i.castSucc) (c i.succ) ⊆ (G i).source ∧
          StrictMonoOn (G i) (G i).source ∧ ContDiffOn ℝ ∞ (G i) (G i).source ∧
          (∀ t ∈ (G i).source, L i (g t) = (G i t, f i (G i t))) ∧
          G i '' Icc (c i.castSucc) (c i.succ) =
            Icc (G i (c i.castSucc)) (G i (c i.succ)) ∧
          Icc (G i (c i.castSucc)) (G i (c i.succ)) ⊆ (G i).target) ∧
        (∀ i, delta ≤ (P i).radius ∧
          Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ (F i).source ∧
          (fun t => F i (t, 0)) '' Icc (0 : ℝ) 1 =
            g '' Icc (c i.castSucc) (c i.succ)) ∧
        (∀ i j : Fin n, i.succ < j.castSucc →
          Disjoint (F i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta))
            (F j '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta))) ∧
        (∀ i j : Fin n, i.succ = j.castSucc →
          ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ z w : ℝ, |z| < delta → |w| < delta →
            F i (t, z) = F j (s, w) → t = 1 ∧ s = 0) ∧
        ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) delta,
          F i (t, z) ∈ closure U ∧ (0 < z → F i (t, z) ∈ U) := by
  classical
  obtain ⟨g, l, u, horient, hg', hend', hinj', hfull, hl, hlu, hu, hreg, hray⟩ :=
    m64Intrinsic_exists_inward_loop_orientation hg hend hinj hab ha hb hregular
      hU hV hdisj hfU hfV
  have hinterval : Icc l u ⊆ Ico (0 : ℝ) T :=
    fun _ ht => ⟨hl.le.trans ht.1, ht.2.trans_lt hu⟩
  have hi : InjOn g (Icc l u) := hinj'.mono hinterval
  obtain ⟨n, c, L, G, f, hf, P, rho, hrho, hn, hc, hfirst, hlast,
    hgraph, hstrip, hseparate, hadj⟩ := m64Intrinsic_exists_separated_arc_strips hg' hlu hi hreg
  let F (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
  have hstep (i : Fin n) : c i.castSucc < c i.succ := hc Fin.castSucc_lt_succ
  have hcut (k : Fin (n + 1)) : c k ∈ Icc l u := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hfU' : frontier U = g '' Icc 0 T := hfU.trans hfull.symm
  have hinward (i : Fin n) : ∃ d > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) d,
        (t, z) ∈ (F i).source ∧ F i (t, z) ∈ closure U ∧
          (0 < z → F i (t, z) ∈ U) := by
    apply m64Intrinsic_exists_inward_graph_strip hg'.continuous hend' hinj' (hstep i)
      (hl.trans_le (hcut i.castSucc).1) ((hcut i.succ).2.trans_lt hu) hU hfU'
      (L i) (G i) (hf i) (hgraph i).1 (hgraph i).2.1 (hgraph i).2.2.2.1
      (hgraph i).2.2.2.2.1 (hgraph i).2.2.2.2.2 (P i)
    simpa only [Prod.eta, (L i).symm_apply_apply] using hray _ (hcut i.castSucc)
  choose width hwidth hregion using hinward
  obtain ⟨epsilon, hepsilon, hle⟩ := exists_pos_le_finite_family width hwidth
  let delta := min rho epsilon
  have hdelta : 0 < delta := lt_min hrho hepsilon
  have hdr : delta ≤ rho := min_le_left _ _
  have hdw (i : Fin n) : delta ≤ width i := (min_le_right _ _).trans (hle i)
  have hrect : Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆
      Icc (0 : ℝ) 1 ×ˢ Ioo (-rho) rho :=
    prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg hdr) hdr)
  refine ⟨g, l, u, n, c, L, G, f, hf, P, horient, hg', hend', hinj', hfull,
    hl, hlu, hu, delta, hdelta, hn, hc, hfirst, hlast, hgraph,
    fun i => ⟨hdr.trans (hstrip i).1, hrect.trans (hstrip i).2.1, (hstrip i).2.2⟩,
    fun i j hij => (hseparate i j hij).mono (image_mono hrect) (image_mono hrect),
    ?_, ?_⟩
  · intro i j hij t ht s hs z w hz hw heq
    exact hadj i j hij t ht s hs z w (hz.trans_le hdr) (hw.trans_le hdr) heq
  · intro i t ht z hz
    exact (hregion i t ht z ⟨hz.1, hz.2.trans (hdw i)⟩).2

end PoincareConjecture
