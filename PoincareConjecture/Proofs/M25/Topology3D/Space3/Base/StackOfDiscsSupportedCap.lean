import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsSupportedMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapTransfer











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_stackCanonicalCapIsotopy
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
      ∃ K : Set (ℝ × E2),
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
        ∀ s sigma lambda gamma rFlat rOne v0 v1 : ℝ,
          |sigma| = 1 → 0 < lambda → lambda < gamma →
          a ≤ s - gamma → s + gamma ≤ b →
          0 < rFlat → 1 - delta < rFlat → rFlat < rOne → rOne < 1 →
          0 < v0 → v0 < v1 → v1 < 1 → v1 ^ 2 + rOne ^ 2 < 1 →
          let ah := stackCanonicalHorizontal v0 v1
          let bv := stackCanonicalVertical rFlat rOne
          let M := stackCapProfilePath ah ah bv bv 0
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          let Y := (fun q : UnitTwoSphere =>
            (s + sigma * lambda * (M (heightCoordinates (q : E3))).2,
              (M (heightCoordinates (q : E3))).1)) '' Qminus
          Y ⊆ T.source ∧ Y ⊆ G.source ∧
            Psi 1 '' (G '' Y) = T '' Y ∧ (Psi 1).symm '' (T '' Y) = G '' Y := by
  obtain ⟨delta, hd, hdq, Psi, K, Q, hK, hKW, hKband, hPsi, hPsii,
      hPsi0, hSupport, hFix, hHeight, hCircle, hQs, _hQt, hQ, hQi, hQh,
      _hProduct, hImages, hmatch⟩ :=
    exists_stackAnnularMatchedIsotopy T G hT hTi hG hGi hTh hGh
      A a b B hAa hab hbB hTs hGs hboundary W hW hWG hCW
  refine ⟨delta, hd, hdq, Psi, K, hK, hKW, hKband, hPsi, hPsii,
    hPsi0, hSupport, hFix, hHeight, hCircle, ?_⟩
  intro s sigma lambda gamma rFlat rOne v0 v1 hsigma hlambda hlg hleft hright
    hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
  have hinner : Icc (s - gamma) (s + gamma) ⊆ Icc a b :=
    fun _ hz => ⟨hleft.trans hz.1, hz.2.trans hright⟩
  have houter : Icc (s - gamma) (s + gamma) ⊆ Icc A B :=
    fun _ hz => ⟨hAa.le.trans (hinner hz).1, (hinner hz).2.trans hbB.le⟩
  have hTs' : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ T.source :=
    fun _ hp => hTs ⟨houter hp.1, hp.2⟩
  have hQs' : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ Q.source := by
    rw [hQs]
    exact fun _ hp => hGs ⟨houter hp.1, hp.2⟩
  obtain ⟨hYT, hYQ, hTQ⟩ := stackCanonicalCap_image_eq_of_annular_match T Q
    hT hTi hQ hQi hTh hQh s sigma lambda gamma delta hsigma hlambda hlg hd
    hTs' hQs' (fun z hz x hx => (hmatch z (hinner hz) x hx.le).2.symm)
    rFlat rOne v0 v1 hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
  rw [hQs] at hYQ
  obtain ⟨hf, hi⟩ := hImages _ hYQ
  refine ⟨hYT, hYQ, hf.trans hTQ.symm, ?_⟩
  rw [hTQ]
  exact hi

end PoincareConjecture.M25.Topology3D
