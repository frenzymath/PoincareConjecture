import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperEndReplacementProtected

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_upper_end_replacement
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) (z : ℝ)
    (hcz : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < z)
    (hseams : ∀ i : Fin D.capCount, (D.cap i).sign = -1 →
      z < (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal)
    (hlevel : IsConnected
      {q : UnitTwoSphere | ⟪(u : E3), psi (q, 0)⟫_ℝ = z})
    (P : SurgeryCapProfile) (tau : ℝ) (htau : 0 < tau) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let S : Set E3 := range j
    let R : Set E3 := S ∩ {y | H y ≤ z}
    let E : Set E3 := S ∩ {y | z ≤ H y}
    let L := heightPlaneCoordinates u
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun t => (P.horizontal_pos t).ne') (fun x => (P.vertical_pos x).ne')
    ∃ (i : Fin D.capCount) (r gamma o w lambda : ℝ)
      (T : OpenPartialHomeomorph (E2 × ℝ) E3)
      (B : BallNeighborhoodChart E2 E2)
      (A N : BallNeighborhoodChart E3 E3)
      (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (K : Set E3),
    let C := D.cap i
    let ell := C.cutHeight - C.removal
    let shared : Set E3 :=
      (fun q : UnitTwoSphere => T ((P.model q).1, z - lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let replacement : Set E3 :=
      (fun q : UnitTwoSphere => T ((P.model q).1, z - lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    C.sign = -1 ∧ (∀ k : Fin D.capCount, (D.cap k).sign = -1 ↔ k = i) ∧
    1 < r ∧ 0 < gamma ∧ gamma < (ell - z) / 8 ∧
    0 < o ∧ o ≤ C.overlapWidth ∧ C.scale * o < gamma / 2 ∧
    0 < w ∧ w ≤ C.collarWidth ∧ |C.beta| * w < C.scale / 2 ∧
    0 < lambda ∧ lambda * P.heightBound < tau ∧
    lambda * P.heightBound < z - c ∧ lambda * P.heightBound < gamma ∧
    T.source =
      (C.tube.source ∩ (ball (0 : E2) r ×ˢ Ioi (ell - gamma))) ∪
        (ball (0 : E2) r ×ˢ Iio (ell + gamma)) ∧
    closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
    ContDiffOn ℝ ∞ T T.source ∧ ContDiffOn ℝ ∞ T.symm T.target ∧
    (∀ p ∈ T.source, H (T p) = p.2) ∧
    (∀ y ∈ T.target, (T.symm y).2 = H y) ∧
    (∀ p ∈ C.tube.source, ‖p.1‖ < r → ell - gamma < p.2 →
      T p = C.tube p ∧ C.tube p ∈ T.target ∧ T.symm (C.tube p) = p) ∧
    (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < o →
      j (C.sourceChart q) =
        C.profile.capMap T C.cutHeight C.sign C.removal C.scale q) ∧
    (∀ x : E2, ‖x‖ ≤ 1 / 8 → ∀ s : ℝ, |s| < w →
      psi (C.flatChart x, s) =
        T (x, C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s)) ∧
    (∀ t ∈ Icc (z - gamma) ell,
      T '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) = S ∩ {y | H y = t}) ∧
    (fun x : E2 => L.symm (x, z)) '' B.boundary = S ∩ {y | H y = z} ∧
    T '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
      (fun x : E2 => L.symm (x, z)) '' B.inside ∧
    T '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
      (fun x : E2 => L.symm (x, z)) '' B.closedRegion ∧
    A.boundary = E ∪ shared ∧ N.boundary = replacement ∪ shared ∧
    N.chart.source = {y : E3 |
      ((M (heightCoordinates y)).1, z - lambda * (M (heightCoordinates y)).2) ∈ T.source} ∧
    N.chart.target = T.target ∧
    (∀ y : E3, N.chart y =
      T ((M (heightCoordinates y)).1, z - lambda * (M (heightCoordinates y)).2)) ∧
    (∀ y : E3, N.chart.symm y = heightCoordinates.symm
      (M.symm ((T.symm y).1, (z - (T.symm y).2) / lambda))) ∧
    (∀ t ∈ Icc z ell,
      A.closedRegion ∩ {y | H y = t} =
        T '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ))) ∧
    N.closedRegion ⊆ A.closedRegion ∧
    N.closedRegion ⊆ {y : E3 | |H y - z| < tau} ∧
    Disjoint A.inside S ∧ A.closedRegion ∩ R ⊆ shared ∧
    G '' E = replacement ∧ G.symm '' replacement = E ∧
    (∀ y ∈ shared ∪ R, G y = y ∧ G.symm y = y) ∧
    IsCompact K ∧ K ⊆ (shared ∪ R)ᶜ ∧
    tsupport (fun y => G y - y) ⊆ K ∧
    tsupport (fun y => G.symm y - y) ⊆ K ∧
    G '' S = R ∪ replacement ∧ G.symm '' (R ∪ replacement) = S ∧
    IsCollarEmbedding (fun p => G (psi p)) := by
  obtain ⟨i, r, gamma, o, w, lambda, T, B, A, N, G, K, hsign, hunique,
    hr, hg, hgap, ho, how, hos, hw, hww, hwb, hl, hlt, hlc, hlg,
    hTsource, hTs, hT, hTi, hTh, hTih, hTold, hcentral, hcollar, hcircle,
    hBboundary, hBinside, hBclosed, hAb, hNb, hNsource, hNtarget, hNpoint, hNinv,
    hAcut, hContain, hShort, _hAlower, hAvoid, hRetained, hGE, hGinv, hGfix,
    hK, hKsub, hKs, hKis, hGS, hGSi, hEmbedding⟩ :=
    exists_saddle_upper_end_replacement_protected psi hpsi u D z hcz hseams hlevel
      P tau htau ∅ isClosed_empty (by simp)
  simp only [union_empty] at hGfix hKsub
  exact ⟨i, r, gamma, o, w, lambda, T, B, A, N, G, K, hsign, hunique,
    hr, hg, hgap, ho, how, hos, hw, hww, hwb, hl, hlt, hlc, hlg,
    hTsource, hTs, hT, hTi, hTh, hTih, hTold, hcentral, hcollar, hcircle,
    hBboundary, hBinside, hBclosed, hAb, hNb, hNsource, hNtarget, hNpoint, hNinv,
    hAcut, hContain, hShort, hAvoid, hRetained, hGE, hGinv, hGfix,
    hK, hKsub, hKs, hKis, hGS, hGSi, hEmbedding⟩

end PoincareConjecture.M25.Topology3D
