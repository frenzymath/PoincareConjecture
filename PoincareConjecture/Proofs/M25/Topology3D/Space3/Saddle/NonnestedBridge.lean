import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ShortPiece
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedRawMiddle
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedEndAssembly










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix NNReal

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞



theorem exists_saddle_nonnested_bridge_witness
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hshort : ∀ q : UnitTwoSphere,
      |⟪(u : E3), psi (q, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| < epsilon) :
    ∃ (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
      (A : Diffeomorph 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, E3) ((ℝ × ℝ) × ℝ) E3 ∞)
      (Kmid : D3),
      Kmid '' Set.range (fun q : UnitTwoSphere => psi (q, 0)) =
        A '' (nonnestedReferenceBallChart 0 d hd).boundary := by
  classical
  have _hBudget := And.intro hepsilon hshort
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  obtain ⟨sigma, d, hd, rho, aRef, delta, eMiddle, J2, gRef, Aref, Gmiddle, Cmiddle,
    hsigma, hsigmaSmall, hdCompact, hdSupport, hdNear, hdZero, hdBounds, hdDeriv,
    hrho, haRef, haCorrection, haLarge, haLocal, haUnit, hJ2, hAref, hArefInv,
    hArefHeight, hRefBoundary, hdelta, hLowerCut, hSmall,
    heMiddle, heMiddleSmall, hCmiddle, hGmiddle, hGmiddleInv, hGmiddleZero,
    hGmiddleHeight, hGmiddleSupport, hGmiddleDisc, hGmiddleLevels,
    hGmiddleClosed, hGmiddleClosedInv, hGmiddleOpen, hGmiddleOpenInv⟩ :=
    exists_saddle_nonnested_raw_middle hP psi hpsi u D W hnonnested
  let nu : ℝ := rho ^ 2 * aRef ^ 2
  have hnu : 0 < nu := mul_pos (sq_pos_of_pos hrho) (sq_pos_of_pos haRef)
  have hcut : W.level < ⟪(u : E3), psi (D.point, 0)⟫_ℝ - delta := by
    change W.level < c - delta
    exact hLowerCut
  have hA : ∀ x : (ℝ × ℝ) × ℝ,
      ⟪(u : E3), Aref x⟫_ℝ = ⟪(u : E3), psi (D.point, 0)⟫_ℝ + nu * x.2 := by
    intro x
    change H (Aref x) = c + (rho ^ 2 * aRef ^ 2) * x.2
    exact hArefHeight x
  have hGheight : ∀ y : E3,
      ⟪(u : E3), Gmiddle 1 y⟫_ℝ = ⟪(u : E3), y⟫_ℝ := by
    intro y
    change H (Gmiddle 1 y) = H y
    exact (hGmiddleHeight 1 y).1
  have hGlevels : ∀ t : ℝ, |t| ≤ delta →
      Gmiddle 1 '' (Set.range (fun q : UnitTwoSphere =>
        Aref (nonnestedReferenceDiffeomorph 0 d hd (q : E3))) ∩
          {y : E3 | ⟪(u : E3), y⟫_ℝ = ⟪(u : E3), psi (D.point, 0)⟫_ℝ + t}) =
        Set.range (fun q : UnitTwoSphere => psi (q, 0)) ∩
          {y : E3 | ⟪(u : E3), y⟫_ℝ = ⟪(u : E3), psi (D.point, 0)⟫_ℝ + t} := by
    intro t ht
    change Gmiddle 1 '' (Set.range (fun q : UnitTwoSphere =>
      Aref (nonnestedReferenceDiffeomorph 0 d hd (q : E3))) ∩
        {y : E3 | H y = c + t}) = Set.range j ∩ {y : E3 | H y = c + t}
    exact (hGmiddleLevels t ht).1
  obtain ⟨Kmid, hKmid⟩ := exists_saddle_nonnested_end_assembly
    hP psi hpsi u D W hnonnested sigma hsigma hsigmaSmall d hd
    hdNear hdZero hdBounds hdDeriv J2 hJ2 Aref nu delta hnu hdelta
    hcut hA (Gmiddle 1) hGheight hGlevels
  exact ⟨d, hd, Aref, Kmid, hKmid⟩

end PoincareConjecture.M25.Topology3D
