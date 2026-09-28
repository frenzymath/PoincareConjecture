import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InwardBandChain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseStripSeparation
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseInwardRay

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem slice_image (F : ℝ × ℝ → AnnulusCoordinates) (h : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    F '' ({q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ h q.1} ∩
      {q | q.1 = t}) = (fun z => F (t, z)) '' Icc (0 : ℝ) (h t) := by
  ext p
  constructor
  · rintro ⟨⟨s, z⟩, ⟨⟨hs, hz⟩, hst⟩, heq⟩
    change s = t at hst
    subst s
    exact ⟨z, hz, heq⟩
  · rintro ⟨z, hz, heq⟩
    exact ⟨(t, z), ⟨⟨ht, hz⟩, rfl⟩, heq⟩

theorem m64Intrinsic_exists_inward_transverse_band_chain
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a < b) (ha : 0 < a) (hb : b < T)
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hfront : frontier U = gamma '' Icc 0 T)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      gamma t + r • quarterTurn (deriv gamma t) ∈ U)
    (d : ℝ → AnnulusCoordinates)
    (hd : ∀ t ∈ Icc a b, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t)) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
      (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      ∃ epsilon > 0, ∀ r : Fin (n + 1) → ℝ, (∀ k, r k ∈ Ioo (0 : ℝ) epsilon) →
        ∃ B : ∀ i : Fin n,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f i) (G i (c i.castSucc)) (G i (c i.succ))
            (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
            (L i (d (c i.succ))).1 (L i (d (c i.succ))).2
            (r i.castSucc) (r i.succ),
          (∀ i, (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
            (B i).leftCut = segment ℝ (gamma (c i.castSucc))
              (gamma (c i.castSucc) + r i.castSucc • d (c i.castSucc)) ∧
            (B i).rightCut = segment ℝ (gamma (c i.succ))
              (gamma (c i.succ) + r i.succ • d (c i.succ)) ∧
            (B i).carrier ⊆ closure U ∧ (B i).carrier \ (B i).lowerArc ⊆ U) ∧
          (∀ i j : Fin n, i.succ < j.castSucc → Disjoint (B i).carrier (B j).carrier) ∧
          ∀ i j : Fin n, i.succ = j.castSucc →
            (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
              (gamma (c i.succ) + r i.succ • d (c i.succ)) := by
  classical
  have hI : Icc a b ⊆ Ico (0 : ℝ) T :=
    fun _ ht => ⟨ha.le.trans ht.1, ht.2.trans_lt hb⟩
  obtain ⟨n, c, L, G, f, hf, P, rho, hrho, hn, hc, hfirst, hlast,
    hgraph, hstrip, hdisjoint, hadj⟩ :=
    m64Intrinsic_exists_separated_transverse_arc_strips hg hab (hinj.mono hI)
      (fun t ht => hregular t ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩) d hd
  let F (i : Fin n) := (P i).linearCoordinates (L i).symm (G i).open_target (hf i)
  have hstep (i : Fin n) := hc (Fin.castSucc_lt_succ (i := i))
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a b := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hleft (i : Fin n) := (hgraph i).1 (left_mem_Icc.mpr (hstep i).le)
  have hright (i : Fin n) := (hgraph i).1 (right_mem_Icc.mpr (hstep i).le)
  have hinward (i : Fin n) : ∃ s > 0,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) s,
        (t, z) ∈ (F i).source ∧ F i (t, z) ∈ closure U ∧
          (0 < z → F i (t, z) ∈ U) := by
    apply m64Intrinsic_exists_inward_graph_strip hg.continuous hend hinj (hstep i)
      (ha.trans_le (hcut i.castSucc).1) ((hcut i.succ).2.trans_lt hb) hU hfront
      (L i) (G i) (hf i) (hgraph i).1 (hgraph i).2.1 (hgraph i).2.2.2.1
      (hgraph i).2.2.2.2.1 (hgraph i).2.2.2.2.2 (P i)
    simpa only [Prod.eta, (L i).symm_apply_apply] using
      m64Intrinsic_transverse_ray_enters_region hg hend hinj hregular hU hfront hray
        ⟨ha.trans_le (hcut i.castSucc).1, (hcut i.castSucc).2.trans_lt hb⟩
        (hd _ (hcut i.castSucc))
  choose width hwidth hregion using hinward
  obtain ⟨eta, heta, hetale⟩ := exists_pos_le_finite_family width hwidth
  let delta := min rho eta
  have hdelta : 0 < delta := lt_min hrho heta
  have hdr : delta ≤ rho := min_le_left _ _
  have hdw (i : Fin n) : delta ≤ width i := (min_le_right _ _).trans (hetale i)
  have hpositive (i : Fin n) := (hgraph i).2.1 (hleft i) (hright i) (hstep i)
  have hbands (i : Fin n) := m64Intrinsic_exists_thin_graph_bands
    (L i).symm (G i).open_target (hf i) (hpositive i)
    (hgraph i).2.2.2.2.2 (P i) hdelta
  choose cutoff hcutoff hbands using hbands
  obtain ⟨epsilon, hepsilon, hle⟩ := exists_pos_le_finite_family cutoff hcutoff
  refine ⟨n, c, L, G, f, hn, hc, hfirst, hlast, epsilon, hepsilon, ?_⟩
  intro r hr
  choose B hB using fun i => hbands i (r i.castSucc)
    ⟨(hr i.castSucc).1, (hr i.castSucc).2.trans_le (hle i)⟩ (r i.succ)
    ⟨(hr i.succ).1, (hr i.succ).2.trans_le (hle i)⟩
  have hcoordinates (i : Fin n) (q : AnnulusCoordinates) :
      (B i).coordinates q = F i (collarParameterEquiv q) := (hB i).2.2.1 q
  have hheight (i : Fin n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (B i).height t < delta := (hB i).2.2.2.1 t ht
  have hcarrier (i : Fin n) : (B i).carrier = F i ''
      {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ (B i).height q.1} :=
    (hB i).2.2.2.2.1
  have hbottom (i : Fin n) : (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) := by
    change (fun x => (L i).symm
      (collarParameterEquiv (collarParameterEquiv.symm (x, f i x)))) ''
        Icc (G i (c i.castSucc)) (G i (c i.succ)) = _
    simp only [collarParameterEquiv.apply_symm_apply]
    rw [← (hgraph i).2.2.2.2.1, image_image]
    exact image_congr (fun t ht => by
      rw [← (hgraph i).2.2.2.1 t ((hgraph i).1 ht), (L i).symm_apply_apply])
  have hcuts (i : Fin n) :
      (B i).leftCut = segment ℝ (gamma (c i.castSucc))
        (gamma (c i.castSucc) + r i.castSucc • d (c i.castSucc)) ∧
      (B i).rightCut = segment ℝ (gamma (c i.succ))
        (gamma (c i.succ) + r i.succ • d (c i.succ)) := by
    constructor
    · rw [(hB i).2.2.2.2.2.1, ← (hgraph i).2.2.2.1 _ (hleft i)]
      simp only [Prod.eta, (L i).symm_apply_apply]
    · rw [(hB i).2.2.2.2.2.2, ← (hgraph i).2.2.2.1 _ (hright i)]
      simp only [Prod.eta, (L i).symm_apply_apply]
  have hsub (i : Fin n) : (B i).carrier ⊆ F i '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-rho) rho) := by
    rw [hcarrier]
    apply image_mono
    intro q hq
    exact ⟨hq.1, ⟨by linarith [hq.2.1], (hq.2.2.trans_lt (hheight i q.1 hq.1)).trans_le hdr⟩⟩
  refine ⟨B, ?_, fun i j hij => (hdisjoint i j hij).mono (hsub i) (hsub j), ?_⟩
  · intro i
    refine ⟨hbottom i, (hcuts i).1, (hcuts i).2, ?_, ?_⟩
    · rw [hcarrier]
      rintro _ ⟨q, hq, rfl⟩
      exact (hregion i q.1 hq.1 q.2
        ⟨hq.2.1, (hq.2.2.trans_lt (hheight i q.1 hq.1)).le.trans (hdw i)⟩).2.1
    · rintro p ⟨hp, hpnot⟩
      rw [hcarrier] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      have hqpos : 0 < q.2 := by
        by_contra hn
        have hz : q.2 = 0 := le_antisymm (le_of_not_gt hn) hq.2.1
        apply hpnot
        rw [hbottom, ← (hstrip i).2.2]
        exact ⟨q.1, hq.1, by rw [← hz]⟩
      exact (hregion i q.1 hq.1 q.2
        ⟨hq.2.1, (hq.2.2.trans_lt (hheight i q.1 hq.1)).le.trans (hdw i)⟩).2.2 hqpos
  · intro i j hij
    rw [hcarrier, hcarrier]
    apply image_inter_eq_of_endpoint_separation
    · intro q hq u hu heq
      apply hadj i j hij q.1 hq.1 u.1 hu.1 q.2 u.2
      · rw [abs_of_nonneg hq.2.1]
        exact (hq.2.2.trans_lt (hheight i q.1 hq.1)).trans_le hdr
      · rw [abs_of_nonneg hu.2.1]
        exact (hu.2.2.trans_lt (hheight j u.1 hu.1)).trans_le hdr
      · exact heq
    · rw [slice_image _ _ (by simp)]
      rw [← (hcuts i).2, ← (B i).right_height_image]
      apply image_congr
      intro z _
      rw [hcoordinates, collarParameterEquiv.apply_symm_apply]
    · rw [slice_image _ _ (by simp)]
      have hcut' : (B j).leftCut = segment ℝ (gamma (c i.succ))
          (gamma (c i.succ) + r i.succ • d (c i.succ)) := by
        rw [hij]
        exact (hcuts j).1
      rw [← hcut', ← (B j).left_height_image]
      apply image_congr
      intro z _
      rw [hcoordinates, collarParameterEquiv.apply_symm_apply]

end PoincareConjecture
