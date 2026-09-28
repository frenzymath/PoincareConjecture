import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseArcCuts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem adjacent_transverse_width
    {gamma : ℝ → AnnulusCoordinates} {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (hinj : InjOn gamma (Icc a c))
    (d : ℝ → AnnulusCoordinates)
    (L R : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G H : OpenPartialHomeomorph ℝ ℝ) {f g : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f G.target) (hg : ContDiffOn ℝ ∞ g H.target)
    (hI : Icc a b ⊆ G.source) (hJ : Icc b c ⊆ H.source)
    (hG : StrictMonoOn G G.source) (hH : StrictMonoOn H H.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    (hgraph' : ∀ t ∈ H.source, R (gamma t) = (H t, g (H t)))
    (himage : G '' Icc a b = Icc (G a) (G b))
    (himage' : H '' Icc b c = Icc (H b) (H c))
    (htarget : Icc (G a) (G b) ⊆ G.target)
    (htarget' : Icc (H b) (H c) ⊆ H.target)
    (hsep : 0 < inner ℝ (-quarterTurn (d b)) (L.symm (1, deriv f (G b))))
    (hsep' : 0 < inner ℝ (-quarterTurn (d b)) (R.symm (1, deriv g (H b))))
    (P : TransverseGraphCuts f (G a) (G b)
      (L (d a)).1 (L (d a)).2 (L (d b)).1 (L (d b)).2)
    (Q : TransverseGraphCuts g (H b) (H c)
      (R (d b)).1 (R (d b)).2 (R (d c)).1 (R (d c)).2) :
    ∃ delta > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < delta → |w| < delta →
        P.linearCoordinates L.symm G.open_target hf (t, z) =
          Q.linearCoordinates R.symm H.open_target hg (s, w) → t = 1 ∧ s = 0 := by
  have haG := hI (left_mem_Icc.mpr hab.le)
  have hbG := hI (right_mem_Icc.mpr hab.le)
  have hbH := hJ (left_mem_Icc.mpr hbc.le)
  have hcH := hJ (right_mem_Icc.mpr hbc.le)
  have hbase : ∀ x ∈ Icc (G a) (G b), ∀ y ∈ Icc (H b) (H c),
      L.symm (x, f x) = R.symm (y, g y) → x = G b ∧ y = H b := by
    intro x hx y hy heq
    obtain ⟨u, hu, rfl⟩ := (himage ▸ hx : x ∈ G '' Icc a b)
    obtain ⟨v, hv, rfl⟩ := (himage' ▸ hy : y ∈ H '' Icc b c)
    rw [← hgraph u (hI hu), ← hgraph' v (hJ hv),
      L.symm_apply_apply, R.symm_apply_apply] at heq
    have huv := hinj ⟨hu.1, hu.2.trans hbc.le⟩ ⟨hab.le.trans hv.1, hv.2⟩ heq
    have hub : u = b := le_antisymm hu.2 (huv ▸ hv.1)
    have hvb : v = b := huv.symm.trans hub
    simp only [hub, hvb, and_self]
  obtain ⟨delta, hdelta, hsep⟩ := exists_adjacent_linear_oblique_width P Q L.symm R.symm
    G.open_target hf H.open_target hg (hG haG hbG hab) htarget (hH hbH hcH hbc) htarget'
    (by rw [← hgraph b hbG, ← hgraph' b hbH, L.symm_apply_apply, R.symm_apply_apply])
    (by simp only [Prod.eta, L.symm_apply_apply, R.symm_apply_apply]) hbase
    (innerSL ℝ (-quarterTurn (d b))) (by
      simp only [Prod.eta, L.symm_apply_apply]
      change inner ℝ (-quarterTurn (d b)) (d b) = 0
      rw [inner_neg_left, real_inner_comm, inner_quarterTurn_self, neg_zero]) hsep hsep'
  exact ⟨delta, hdelta, fun t ht s hs z w hz hw heq =>
    (hsep t ht s hs z w hz hw).2.2 heq⟩

private theorem dependent_transport {X : Type*} {A : X → Sort*} {Y : Sort*}
    (f : ∀ x, A x → Y) {x y : X} (h : x = y) (p : A y) :
    f x (h.symm ▸ p) = f y p := by cases h; rfl

theorem m64Intrinsic_exists_separated_transverse_arc_strips
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {a b : ℝ} (hab : a < b) (hinj : InjOn gamma (Icc a b))
    (hregular : ∀ t ∈ Icc a b, deriv gamma t ≠ 0)
    (d : ℝ → AnnulusCoordinates)
    (hd : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t)) :
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
        ∀ i j : Fin n, i.succ = j.castSucc →
          ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ z w : ℝ, |z| < delta → |w| < delta →
            F i (t, z) = F j (s, w) → t = 1 ∧ s = 0 := by
  classical
  obtain ⟨n, c, L, G, f, hn, hc, hfirst, hlast, hpieces⟩ :=
    m64Intrinsic_exists_arc_transverse_cut_subdivision hg hab hregular d hd
  have hI (i : Fin n) := (hpieces i).1
  have hmono (i : Fin n) := (hpieces i).2.1
  have hG (i : Fin n) := (hpieces i).2.2.1
  have hf (i : Fin n) := (hpieces i).2.2.2.1
  have hgraph (i : Fin n) := (hpieces i).2.2.2.2.1
  have himage (i : Fin n) := (hpieces i).2.2.2.2.2.1
  have htarget (i : Fin n) := (hpieces i).2.2.2.2.2.2.1
  have htrans (i : Fin n) := (hpieces i).2.2.2.2.2.2.2.1
  let P (i : Fin n) := Classical.choice (hpieces i).2.2.2.2.2.2.2.2
  let F (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
  have hstep (i : Fin n) : c i.castSucc < c i.succ := hc Fin.castSucc_lt_succ
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hGi (i : Fin n) : G i (c i.castSucc) < G i (c i.succ) :=
    hmono i (hI i (left_mem_Icc.mpr (hstep i).le))
      (hI i (right_mem_Icc.mpr (hstep i).le)) (hstep i)
  have haxis (i : Fin n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, (0 : ℝ)) ∈ (F i).source :=
    (P i).linearCoordinates_axis_mem_source (L i).symm (G i).open_target (hf i)
      (hGi i) (htarget i) ht
  have haxis_image (i : Fin n) : (fun t => F i (t, 0)) '' Icc (0 : ℝ) 1 =
      gamma '' Icc (c i.castSucc) (c i.succ) :=
    m64Intrinsic_graph_strip_axis_image (L i) (G i) (hf i) (hI i) (hGi i).le
      (hgraph i) (himage i) (P i)
  have hseparate (i j : Fin n) (hij : i.succ < j.castSucc) :
      Disjoint ((fun t => F i (t, 0)) '' Icc (0 : ℝ) 1)
        ((fun t => F j (t, 0)) '' Icc (0 : ℝ) 1) := by
    rw [haxis_image, haxis_image]
    apply disjoint_left.mpr
    rintro p ⟨t, ht, htp⟩ ⟨s, hs, hsp⟩
    have hts := hinj ⟨(hcut i.castSucc).1.trans ht.1, ht.2.trans (hcut i.succ).2⟩
      ⟨(hcut j.castSucc).1.trans hs.1, hs.2.trans (hcut j.succ).2⟩ (htp.trans hsp.symm)
    have hlt := hc hij
    linarith [ht.2, hs.1]
  let J := {p : Fin n × Fin n // p.1.succ = p.2.castSucc}
  have hadj (p : J) : ∃ r > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < r → |w| < r →
        F p.1.1 (t, z) = F p.1.2 (s, w) → t = 1 ∧ s = 0 := by
    let i := p.1.1
    let j := p.1.2
    have he : c i.succ = c j.castSucc := congrArg c p.2
    have hbc : c i.succ < c j.succ := by rw [he]; exact hstep j
    have hsub : InjOn gamma (Icc (c i.castSucc) (c j.succ)) :=
      hinj.mono (Icc_subset_Icc (hcut i.castSucc).1 (hcut j.succ).2)
    have hJ : Icc (c i.succ) (c j.succ) ⊆ (G j).source := by rw [he]; exact hI j
    have himage' : G j '' Icc (c i.succ) (c j.succ) =
        Icc (G j (c i.succ)) (G j (c j.succ)) := by rw [he]; exact himage j
    have htarget' : Icc (G j (c i.succ)) (G j (c j.succ)) ⊆ (G j).target := by
      rw [he]; exact htarget j
    have hsep' : 0 < inner ℝ (-quarterTurn (d (c i.succ)))
        ((L j).symm (1, deriv (f j) (G j (c i.succ)))) := by
      rw [he]
      exact (htrans j _ (left_mem_Icc.mpr (hstep j).le)).2.2
    let Q : TransverseGraphCuts (f j) (G j (c i.succ)) (G j (c j.succ))
        (L j (d (c i.succ))).1 (L j (d (c i.succ))).2
        (L j (d (c j.succ))).1 (L j (d (c j.succ))).2 := he.symm ▸ P j
    obtain ⟨r, hr, hsep⟩ := adjacent_transverse_width
      (hstep i) hbc hsub d (L i) (L j) (G i) (G j) (hf i) (hf j)
      (hI i) hJ (hmono i) (hmono j) (hgraph i) (hgraph j) (himage i) himage'
      (htarget i) htarget' (htrans i _ (right_mem_Icc.mpr (hstep i).le)).2.2 hsep' (P i) Q
    have hQ : Q.linearCoordinates (L j).symm (G j).open_target (hf j) = F j :=
      dependent_transport
        (A := fun t => TransverseGraphCuts (f j) (G j t) (G j (c j.succ))
          (L j (d t)).1 (L j (d t)).2
          (L j (d (c j.succ))).1 (L j (d (c j.succ))).2)
        (fun _ R => R.linearCoordinates (L j).symm (G j).open_target (hf j)) he (P j)
    refine ⟨r, hr, fun t ht s hs z w hz hw heq => ?_⟩
    apply hsep t ht s hs z w hz hw
    simpa only [hQ] using heq
  choose width hwidth hsep using hadj
  obtain ⟨epsilon, hepsilon, hle⟩ := exists_pos_le_finite_family width hwidth
  obtain ⟨delta, hdelta, hbound, hsource, hdisjoint⟩ :=
    exists_finite_disjoint_strip_width F haxis (fun i j => i.succ < j.castSucc)
      hseparate (fun i => min (P i).radius epsilon)
      (fun i => lt_min (P i).radius_pos hepsilon)
  refine ⟨n, c, L, G, f, hf, P, delta, hdelta, hn, hc, hfirst, hlast,
    fun i => ⟨hI i, hmono i, hG i, hgraph i, himage i, htarget i⟩,
    fun i => ⟨(hbound i).trans (min_le_left _ _), hsource i, haxis_image i⟩,
    hdisjoint, ?_⟩
  intro i j hij t ht s hs z w hz hw heq
  let p : J := ⟨(i, j), hij⟩
  have hdw : delta ≤ width p := ((hbound i).trans (min_le_right _ _)).trans (hle p)
  exact hsep p t ht s hs z w (hz.trans_le hdw) (hw.trans_le hdw) heq

end PoincareConjecture
