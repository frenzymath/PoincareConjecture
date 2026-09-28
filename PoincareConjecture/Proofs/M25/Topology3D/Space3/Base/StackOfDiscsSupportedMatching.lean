import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsAnnularSupport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsPhaseTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyTransport

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackAnnularMatchedIsotopy
    (T G : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hG : ContDiffOn ℝ ∞ G G.source) (hGi : ContDiffOn ℝ ∞ G.symm G.target)
    (hTh : ∀ p ∈ T.source, (T p).1 = p.1)
    (hGh : ∀ p ∈ G.source, (G p).1 = p.1)
    (A a b B : ℝ) (hAa : A < a) (hab : a < b) (hbB : b < B)
    (hTs : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ T.source)
    (hGs : Icc A B ×ˢ closedBall (0 : E2) 1 ⊆ G.source)
    (hboundary : ∀ z ∈ Icc A B, ∀ q ∈ sphere (0 : E2) 1, T (z, q) = G (z, q))
    (W : Set (ℝ × E2)) (hW : IsOpen W) (hWG : W ⊆ G.source)
    (hCW : Icc A B ×ˢ sphere (0 : E2) 1 ⊆ W) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 / 4 ∧
      ∃ Psi : ℝ → Diffeomorph 𝓘(ℝ, ℝ × E2) 𝓘(ℝ, ℝ × E2)
        (ℝ × E2) (ℝ × E2) ∞,
      ∃ K : Set (ℝ × E2), ∃ Q : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2),
        IsCompact K ∧ K ⊆ G '' W ∧ K ⊆ Ioo A B ×ˢ (univ : Set E2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E2) => Psi p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × (ℝ × E2) => (Psi p.1).symm p.2) ∧
        (∀ p, Psi 0 p = p) ∧
        (∀ t, tsupport (fun p => Psi t p - p) ⊆ K ∧
          tsupport (fun p => (Psi t).symm p - p) ⊆ K) ∧
        (∀ t p, p ∉ K → Psi t p = p ∧ (Psi t).symm p = p) ∧
        (∀ t p, (Psi t p).1 = p.1 ∧ ((Psi t).symm p).1 = p.1) ∧
        (∀ t z, z ∈ Icc A B → ∀ q ∈ sphere (0 : E2) 1,
          Psi t (G (z, q)) = G (z, q) ∧ (Psi t).symm (G (z, q)) = G (z, q)) ∧
        Q.source = G.source ∧ Q.target = G.target ∧
        ContDiffOn ℝ ∞ Q Q.source ∧ ContDiffOn ℝ ∞ Q.symm Q.target ∧
        (∀ p ∈ Q.source, (Q p).1 = p.1) ∧
        (∀ J : Set ℝ,
          Q '' (J ×ˢ ball (0 : E2) 1) = G '' (J ×ˢ ball 0 1) ∧
          Q '' (J ×ˢ closedBall (0 : E2) 1) = G '' (J ×ˢ closedBall 0 1)) ∧
        (∀ Y : Set (ℝ × E2), Y ⊆ G.source →
          Psi 1 '' (G '' Y) = Q '' Y ∧ (Psi 1).symm '' (Q '' Y) = G '' Y) ∧
        ∀ z ∈ Icc a b, ∀ x : E2, |‖x‖ - 1| ≤ delta →
          (z, x) ∈ Q.source ∧ Q (z, x) = T (z, x) := by
  obtain ⟨delta0, hd0, hd0q, F0, _S0, _hS0c, _hS0b, _hS0f, _hS0i,
      _hFix0, hHeight0, hCircle0, _hQ0s, _hQ0t, _hQ0, _hQ0i,
      _hQ0h, _hQ0ih, hProduct0, hEndpoint0⟩ :=
    exists_stackAnnularMatchedChart T G hT hTi hG hGi hTh hGh
      A a b B hAa hab hbB hTs hGs hboundary
  let g : (ℝ × E2) → E2 := fun p => (F0 p).2
  have hfixed (z : ℝ) (q : E2) (hq : q ∈ sphere (0 : E2) 1) : g (z, q) = q :=
    congrArg Prod.snd (hCircle0 z q hq).1
  have hnormal (z : ℝ) (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      0 < ⟪q, fderiv ℝ (fun y => g (z, y)) q q⟫_ℝ := by
    apply stackHeightChart_normal_pos F0.toHomeomorph.toOpenPartialHomeomorph
      F0.contDiff.contDiffOn F0.symm.contDiff.contDiffOn
      (fun p _ => (hHeight0 p).1) z q (mem_sphere_zero_iff_norm.mp hq) (mem_univ _)
      (fun x hx => hfixed z x (mem_sphere_zero_iff_norm.mpr hx))
    intro x _hx hxnorm
    by_contra hnot
    have hsmall : F0 (z, x) ∈ (univ : Set ℝ) ×ˢ ball (0 : E2) 1 :=
      ⟨mem_univ _, mem_ball_zero_iff.mpr (lt_of_not_ge hnot)⟩
    have hin := mem_image_of_mem F0.symm hsmall
    rw [(hProduct0 univ).2.2.1, F0.symm_apply_apply] at hin
    exact (not_lt_of_ge hxnorm) (mem_ball_zero_iff.mp hin.2)
  obtain ⟨delta1, hd1, _hd1q, e, heq, hes, he, hei, _hAnnU, hTarget, _hinner⟩ :=
    exists_stackAnnularChart_in_open g univ W isOpen_univ hW F0.contDiff.snd.contDiffOn
      A a b B hAa hab hbB (fun _ _ => mem_univ _) hCW
      (fun z _ q hq => hfixed z q hq) (fun z _ q hq => hnormal z q hq)
  obtain ⟨rho, _hrho, _hrhoc, _hrhos, hnear, _hrange, hField, hFieldc,
      hFieldt, hFieldh, hFieldq, _hcoords⟩ :=
    exists_stackAnnularCutoff g A a b B delta1 hAa hab hbB hd1 e heq hes he hei
      (fun z _ q hq => hfixed z q hq)
  obtain ⟨Phi, _H, S, hSeq, hSc, hSband, hPhi, hPhii, hPhi0, hPhih,
      hFiber, _hH, _hHi, hCircle, _hDisc, _hSupport, hFix, _hTrack, hEndpoint, hProduct⟩ :=
    exists_stackAnnularEvolution g A a b B delta1 hAa hab hbB hd1 e heq hes he rho
      hnear hField hFieldc hFieldt hFieldh hFieldq
  have hSW : S ⊆ W := by
    intro p hp
    rw [hSeq] at hp
    rcases hp with ⟨v, hv, rfl⟩
    exact (hTarget (hFieldt hv)).2
  have hSG : S ⊆ G.source := hSW.trans hWG
  have hmap (t : ℝ) : MapsTo (Phi t) G.source G.source :=
    equiv_mapsTo_of_fixed_compl (Phi t).toEquiv
      (fun p hp => (hFix t p (fun hs => hp (hSG hs))).1)
  have hmapi (t : ℝ) : MapsTo (Phi t).symm G.source G.source :=
    equiv_mapsTo_of_fixed_compl (Phi t).symm.toEquiv
      (fun p hp => (hFix t p (fun hs => hp (hSG hs))).2)
  let Psi := fun t => chartConjugateDiffeomorph G hG hGi (Phi t) hSc hSG
    (fun p hp => (hFix t p hp).1)
  let K := G '' S
  have hK : IsCompact K := hSc.image_of_continuousOn (G.continuousOn.mono hSG)
  have hKband : K ⊆ Ioo A B ×ˢ (univ : Set E2) := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hGh p (hSG hp)).symm ▸ (hSband hp).1, mem_univ _⟩
  have hPsiFix (t : ℝ) (p : ℝ × E2) (hp : p ∉ K) :
      Psi t p = p ∧ (Psi t).symm p = p :=
    ⟨chartConjugateMap_eq_self G (Phi t) (fun x hx => (hFix t x hx).1) hp,
      chartConjugateMap_eq_self G (Phi t).symm (fun x hx => (hFix t x hx).2) hp⟩
  have hPsiTrack (t : ℝ) (p : ℝ × E2) (hp : p ∈ G.source) :
      Psi t (G p) = G (Phi t p) ∧ (Psi t).symm (G p) = G ((Phi t).symm p) :=
    ⟨chartConjugateMap_apply_chart G (Phi t) hp,
      chartConjugateMap_apply_chart G (Phi t).symm hp⟩
  have hGih (p : ℝ × E2) (hp : p ∈ G.target) : (G.symm p).1 = p.1 := by
    have hh := hGh (G.symm p) (G.map_target hp)
    rw [G.right_inv hp] at hh
    exact hh.symm
  have hPsiHeight (t : ℝ) (p : ℝ × E2) :
      (Psi t p).1 = p.1 ∧ ((Psi t).symm p).1 = p.1 := by
    by_cases hp : p ∈ G.target
    · have hps := G.map_target hp
      change (chartConjugateMap G (Phi t) p).1 = p.1 ∧
        (chartConjugateMap G (Phi t).symm p).1 = p.1
      rw [chartConjugateMap_of_mem G (Phi t) hp,
        chartConjugateMap_of_mem G (Phi t).symm hp]
      exact ⟨(hGh _ (hmap t hps)).trans ((hPhih t (G.symm p)).1.trans (hGih p hp)),
        (hGh _ (hmapi t hps)).trans ((hPhih t (G.symm p)).2.trans (hGih p hp))⟩
    · have hpK : p ∉ K := by
        rintro ⟨x, hx, rfl⟩
        exact hp (G.map_source (hSG hx))
      rw [(hPsiFix t p hpK).1, (hPsiFix t p hpK).2]
      exact ⟨rfl, rfl⟩
  let Q := (Phi 1).toHomeomorph.toOpenPartialHomeomorph.trans G
  have hQs : Q.source = G.source := by
    ext p
    constructor
    · intro hp
      have hp' : Phi 1 p ∈ G.source := hp.2
      have hpi : (Phi 1).symm (Phi 1 p) ∈ G.source := hmapi 1 hp'
      simpa only [Diffeomorph.symm_apply_apply] using hpi
    · intro hp
      exact ⟨mem_univ _, hmap 1 hp⟩
  have hQt : Q.target = G.target := by
    change G.target ∩ G.symm ⁻¹' univ = G.target
    simp only [preimage_univ, inter_univ]
  let delta := min delta0 delta1
  have hd : 0 < delta := lt_min hd0 hd1
  have hdd0 : delta ≤ delta0 := min_le_left _ _
  have hdd1 : delta ≤ delta1 := min_le_right _ _
  refine ⟨delta, hd, hdd0.trans_lt hd0q, Psi, K, Q, hK, image_mono hSW, hKband,
    ?_, ?_, ?_, ?_, hPsiFix, hPsiHeight, ?_, hQs, hQt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact chartConjugateMap_contDiff_family G hG hGi (fun t => Phi t) hPhi
      hmap hSc hSG (fun t p hp => (hFix t p hp).1)
  · exact chartConjugateMap_contDiff_family G hG hGi (fun t => (Phi t).symm) hPhii
      hmapi hSc hSG (fun t p hp => (hFix t p hp).2)
  · intro p
    change chartConjugateMap G (Phi 0) p = p
    by_cases hp : p ∈ G.target
    · rw [chartConjugateMap_of_mem G (Phi 0) hp, hPhi0, G.right_inv hp]
    · simp only [chartConjugateMap, if_neg hp]
  · intro t
    constructor
    · apply closure_minimal _ hK.isClosed
      intro p hp
      by_contra hn
      exact hp (sub_eq_zero.mpr (hPsiFix t p hn).1)
    · apply closure_minimal _ hK.isClosed
      intro p hp
      by_contra hn
      exact hp (sub_eq_zero.mpr (hPsiFix t p hn).2)
  · intro t z hz q hq
    have hpG : (z, q) ∈ G.source := hGs ⟨hz, sphere_subset_closedBall hq⟩
    have hc : Phi t (z, q) = (z, q) :=
      (hCircle t z q (mem_sphere_zero_iff_norm.mp hq)).1
    have hci : (Phi t).symm (z, q) = (z, q) :=
      equiv_symm_fixed_of_fixed (Phi t).toEquiv hc
    rw [(hPsiTrack t (z, q) hpG).1, (hPsiTrack t (z, q) hpG).2, hc, hci]
    exact ⟨rfl, rfl⟩
  · exact hG.comp (Phi 1).contDiff.contDiffOn (fun _ hp => hp.2)
  · exact (Phi 1).symm.contDiff.comp_contDiffOn (hGi.mono inter_subset_left)
  · intro p hp
    exact (hGh (Phi 1 p) hp.2).trans (hPhih 1 p).1
  · intro J
    constructor
    · calc
        Q '' (J ×ˢ ball (0 : E2) 1) = G '' (Phi 1 '' (J ×ˢ ball 0 1)) :=
          (image_image G (Phi 1) _).symm
        _ = G '' (J ×ˢ ball 0 1) := congrArg (image G) (hProduct 1 J).1
    · calc
        Q '' (J ×ˢ closedBall (0 : E2) 1) = G '' (Phi 1 '' (J ×ˢ closedBall 0 1)) :=
          (image_image G (Phi 1) _).symm
        _ = G '' (J ×ˢ closedBall 0 1) := congrArg (image G) (hProduct 1 J).2.1
  · intro Y hY
    have hf : Psi 1 '' (G '' Y) = Q '' Y := by
      rw [image_image]
      exact image_congr (fun p hp => (hPsiTrack 1 p (hY hp)).1)
    refine ⟨hf, ?_⟩
    calc
      (Psi 1).symm '' (Q '' Y) = (Psi 1).symm '' (Psi 1 '' (G '' Y)) :=
        congrArg (image (Psi 1).symm) hf.symm
      _ = ((Psi 1).symm ∘ Psi 1) '' (G '' Y) := image_image _ _ _
      _ = id '' (G '' Y) := image_congr (fun p _ => (Psi 1).symm_apply_apply p)
      _ = G '' Y := image_id _
  · intro z hz x hx
    have hmatch : Phi 1 (z, x) = F0 (z, x) := by
      apply Prod.ext
      · exact (hPhih 1 (z, x)).1.trans (hHeight0 (z, x)).1.symm
      · exact (hFiber 1 z x).1.symm.trans (hEndpoint z hz x (hx.trans hdd1))
    obtain ⟨hsource0, hequal0⟩ := hEndpoint0 z hz x (hx.trans hdd0)
    refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
    · change Phi 1 (z, x) ∈ G.source
      rw [hmatch]
      exact hsource0.2
    · change G (Phi 1 (z, x)) = T (z, x)
      rw [hmatch]
      exact hequal0

end PoincareConjecture.M25.Topology3D
