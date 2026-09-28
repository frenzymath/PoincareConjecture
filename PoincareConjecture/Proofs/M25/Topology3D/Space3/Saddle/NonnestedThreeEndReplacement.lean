import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedLowerEndReplacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.UpperEndReplacementProtected

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

set_option maxHeartbeats 1000000 in

theorem exists_saddle_nonnested_three_end_replacement
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (z : ℝ) (hcz : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < z)
    (hseams : ∀ i : Fin D.capCount, (D.cap i).sign = -1 →
      z < (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal)
    (hlevel : IsConnected
      {q : UnitTwoSphere | ⟪(u : E3), psi (q, 0)⟫_ℝ = z})
    (P : SurgeryCapProfile) (tau : ℝ) (htau : 0 < tau) :
    let H := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range (fun q : UnitTwoSphere => psi (q, 0))
    let Rmid := S ∩ {y : E3 | W.level ≤ H y ∧ H y ≤ z}
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun t => (P.horizontal_pos t).ne') (fun x => (P.vertical_pos x).ne')
    ∃ (Tlow : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
      (lambdaLow : Fin 2 → ℝ) (Nlow : Fin 2 → BallNeighborhoodChart E3 E3)
      (Tup : OpenPartialHomeomorph (E2 × ℝ) E3) (lambdaUp : ℝ)
      (Nup : BallNeighborhoodChart E3 E3) (G : D3) (K : Set E3),
    let lowerMap := fun (i : Fin 2) (q : UnitTwoSphere) =>
      Tlow i ((P.model q).1, W.level + lambdaLow i * (P.model q).2)
    let upperMap := fun q : UnitTwoSphere =>
      Tup ((P.model q).1, z - lambdaUp * (P.model q).2)
    let south := fun i => lowerMap i ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let north := fun i => lowerMap i ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let replacement := upperMap ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let shared := upperMap ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    (∀ i : Fin 2,
      0 < lambdaLow i ∧ lambdaLow i * P.heightBound < tau ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (Tlow i).source ∧
      ContDiffOn ℝ ∞ (Tlow i) (Tlow i).source ∧
      ContDiffOn ℝ ∞ (Tlow i).symm (Tlow i).target ∧
      (∀ p ∈ (Tlow i).source, H (Tlow i p) = p.2) ∧
      (Nlow i).boundary = south i ∪ north i ∧
      (Nlow i).chart.source = {y : E3 |
        ((M (heightCoordinates y)).1,
          W.level + lambdaLow i * (M (heightCoordinates y)).2) ∈ (Tlow i).source} ∧
      (Nlow i).chart.target = (Tlow i).target ∧
      (∀ y : E3, (Nlow i).chart y = Tlow i ((M (heightCoordinates y)).1,
        W.level + lambdaLow i * (M (heightCoordinates y)).2)) ∧
      (∀ y : E3, (Nlow i).chart.symm y = heightCoordinates.symm
        (M.symm (((Tlow i).symm y).1,
          (((Tlow i).symm y).2 - W.level) / lambdaLow i))) ∧
      (Nlow i).closedRegion ⊆ {y : E3 | |H y - W.level| < tau}) ∧
    0 < lambdaUp ∧ lambdaUp * P.heightBound < tau ∧
    closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ Tup.source ∧
    ContDiffOn ℝ ∞ Tup Tup.source ∧ ContDiffOn ℝ ∞ Tup.symm Tup.target ∧
    (∀ p ∈ Tup.source, H (Tup p) = p.2) ∧
    Nup.boundary = replacement ∪ shared ∧
    Nup.chart.source = {y : E3 |
      ((M (heightCoordinates y)).1, z - lambdaUp * (M (heightCoordinates y)).2) ∈
        Tup.source} ∧
    Nup.chart.target = Tup.target ∧
    (∀ y : E3, Nup.chart y =
      Tup ((M (heightCoordinates y)).1, z - lambdaUp * (M (heightCoordinates y)).2)) ∧
    (∀ y : E3, Nup.chart.symm y = heightCoordinates.symm
      (M.symm ((Tup.symm y).1, (z - (Tup.symm y).2) / lambdaUp))) ∧
    Nup.closedRegion ⊆ {y : E3 | |H y - z| < tau} ∧
    Disjoint (Nlow 0).closedRegion (Nlow 1).closedRegion ∧
    (∀ i : Fin 2, Disjoint (Nlow i).closedRegion Nup.closedRegion) ∧
    G '' S = Rmid ∪ south 0 ∪ south 1 ∪ replacement ∧
    G.symm '' (Rmid ∪ south 0 ∪ south 1 ∪ replacement) = S ∧
    (∀ y ∈ Rmid, G y = y ∧ G.symm y = y) ∧
    IsCompact K ∧ K ⊆ Rmidᶜ ∧
    tsupport (fun y : E3 => G y - y) ⊆ K ∧
    tsupport (fun y : E3 => G.symm y - y) ⊆ K ∧
    IsCollarEmbedding (fun p => G (psi p)) := by
  classical
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S := range (fun q : UnitTwoSphere => psi (q, 0))
  let Rlo := S ∩ {y : E3 | W.level ≤ H y}
  let Eupper := S ∩ {y : E3 | z ≤ H y}
  let Rmid := S ∩ {y : E3 | W.level ≤ H y ∧ H y ≤ z}
  have hwz : W.level < z := W.level_lt_critical.trans hcz
  let eta := min tau ((z - W.level) / 4)
  have heta : 0 < eta := lt_min htau (div_pos (sub_pos.mpr hwz) (by norm_num))
  have hetatau : eta ≤ tau := min_le_left _ _
  have hgap : W.level + eta < z - eta := by
    have h := min_le_right tau ((z - W.level) / 4)
    change eta ≤ (z - W.level) / 4 at h
    linarith
  obtain ⟨Tlow, lambdaLow, Alow, Nlow, Glow, Clow, hlow, hLowdis,
    hLowImage, _hLowInv, hLowFix, _hLowEmbedding⟩ :=
    exists_saddle_nonnested_lower_end_replacement hP psi hpsi u D W hnonnested
      P eta heta
  choose hLpositive hLwidth hLs hLT hLTi hLH hLold hLAb hLNb hLNsource hLNtarget
    hLNpoint hLNinv hLAcut hLcontain hLband hLavoid hLret hLimage hLinv hLfix
    hLC hLCsub hLCs hLCis using hlow
  let south := fun i : Fin 2 =>
    (fun q : UnitTwoSphere => Tlow i
      ((P.model q).1, W.level + lambdaLow i * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let Kcaps := (Nlow 0).closedRegion ∪ (Nlow 1).closedRegion
  have hKcaps : IsClosed Kcaps :=
    ((Nlow 0).closedRegion_compact.union (Nlow 1).closedRegion_compact).isClosed
  have hLowerHeight (i : Fin 2) (y : E3) (hy : y ∈ (Nlow i).closedRegion) :
      H y < z - eta := by
    have hb : |H y - W.level| < eta := hLband i hy
    have h := (abs_lt.mp hb).2
    linarith
  have hKheight : ∀ y ∈ Kcaps, ⟪(u : E3), y⟫_ℝ < z - eta := by
    rintro y (hy | hy)
    · exact hLowerHeight 0 y hy
    · exact hLowerHeight 1 y hy
  obtain ⟨_iup, _r, _gamma, _o, _w, lambdaUp, Tup, _Bup, _Aup, Nup, Gup, Kup,
    _hsign, _hunique, _hr, _hg, _hgap, _ho, _how, _hos, _hw, _hww, _hwb,
    hUpositive, hUwidth, _hUc, _hUg, _hTsource, hUs, hUT, hUTi, hUH, _hUHi,
    _hUold, _hUcentral, _hUcollar, _hUcircle, _hBboundary, _hBinside, _hBclosed,
    _hAb, hUNb, hUNsource, hUNtarget, hUNpoint, hUNinv, _hAcut, _hContain,
    hUband, _hAlower, _hAvoid, _hRetained, hUE, _hUinv, hUfix, hUC, hUCsub,
    hUCs, hUCis, _hUS, _hUSi, _hUEmbedding⟩ :=
    exists_saddle_upper_end_replacement_protected psi hpsi u D z hcz hseams
      hlevel P eta heta Kcaps hKcaps hKheight
  let replacement :=
    (fun q : UnitTwoSphere => Tup ((P.model q).1, z - lambdaUp * (P.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let g : D3 := (Glow 0).trans (Glow 1)
  let G : D3 := g.trans Gup
  let K := (Clow 0 ∪ Clow 1) ∪ Kup
  have hK : IsCompact K := ((hLC 0).union (hLC 1)).union hUC
  have hSouthClosed (i : Fin 2) : south i ⊆ (Nlow i).closedRegion := by
    intro y hy
    rw [← (Nlow i).inside_union_boundary, hLNb i]
    exact Or.inr (Or.inl hy)
  have hSouthCaps (i : Fin 2) : south i ⊆ Kcaps := by
    fin_cases i
    · exact fun _ hy => Or.inl (hSouthClosed 0 hy)
    · exact fun _ hy => Or.inr (hSouthClosed 1 hy)
  have hUmid (y : E3) (hy : y ∈ Rmid) : Gup y = y ∧ Gup.symm y = y :=
    hUfix y (Or.inl (Or.inr ⟨hy.1, hy.2.2⟩))
  have hUcap (i : Fin 2) (y : E3) (hy : y ∈ south i) :
      Gup y = y ∧ Gup.symm y = y := hUfix y (Or.inr (hSouthCaps i hy))
  have hFixedImage (X : Set E3) (hX : ∀ y ∈ X, Gup y = y) : Gup '' X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hX x hx] using hx
    · intro hy
      exact ⟨y, hy, hX y hy⟩
  have hRsplit : Rlo = Rmid ∪ Eupper := by
    ext y
    constructor
    · rintro ⟨hyS, hylo⟩
      rcases le_total (H y) z with hyup | hyup
      · exact Or.inl ⟨hyS, hylo, hyup⟩
      · exact Or.inr ⟨hyS, hyup⟩
    · rintro (⟨hyS, hylo, _⟩ | ⟨hyS, hyup⟩)
      · exact ⟨hyS, hylo⟩
      · exact ⟨hyS, hwz.le.trans hyup⟩
  change g '' S = Rlo ∪ south 0 ∪ south 1 at hLowImage
  change Gup '' Eupper = replacement at hUE
  have hImage : G '' S = Rmid ∪ south 0 ∪ south 1 ∪ replacement := by
    calc
      G '' S = Gup '' (g '' S) := by rw [image_image]; rfl
      _ = Gup '' ((Rmid ∪ Eupper) ∪ south 0 ∪ south 1) := by
        rw [hLowImage, hRsplit]
      _ = (Rmid ∪ replacement) ∪ south 0 ∪ south 1 := by
        rw [image_union, image_union, image_union,
          hFixedImage Rmid (fun y hy => (hUmid y hy).1), hUE,
          hFixedImage (south 0) (fun y hy => (hUcap 0 y hy).1),
          hFixedImage (south 1) (fun y hy => (hUcap 1 y hy).1)]
      _ = Rmid ∪ south 0 ∪ south 1 ∪ replacement := by
        ext y
        simp only [mem_union]
        tauto
  have hFix (y : E3) (hy : y ∈ Rmid) : G y = y ∧ G.symm y = y := by
    have hlo := hLowFix y ⟨hy.1, hy.2.1⟩
    have hup := hUmid y hy
    change Gup (g y) = y ∧ g.symm (Gup.symm y) = y
    change g y = y ∧ g.symm y = y at hlo
    rw [hlo.1, hup.1, hup.2, hlo.2]
    exact ⟨rfl, rfl⟩
  have hKsub : K ⊆ Rmidᶜ := by
    intro y hy hymid
    rcases hy with (hy | hy) | hy
    · exact hLCsub 0 hy (Or.inl (Or.inr ⟨hymid.1, hymid.2.1⟩))
    · exact hLCsub 1 hy (Or.inl (Or.inr ⟨hymid.1, hymid.2.1⟩))
    · exact hUCsub hy (Or.inl (Or.inr ⟨hymid.1, hymid.2.2⟩))
  have hOutside (y : E3) (hy : y ∉ K) : G y = y ∧ G.symm y = y := by
    have hfactor (F : D3) (C : Set E3) (hC : C ⊆ K)
        (hs : tsupport (fun x : E3 => F x - x) ⊆ C)
        (his : tsupport (fun x : E3 => F.symm x - x) ⊆ C) :
        F y = y ∧ F.symm y = y := by
      constructor
      · exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
          (f := fun x : E3 => F x - x)
          (fun h => hy (hC (hs h))))
      · exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
          (f := fun x : E3 => F.symm x - x)
          (fun h => hy (hC (his h))))
    have h0 := hfactor (Glow 0) (Clow 0) (fun _ h => Or.inl (Or.inl h))
      (hLCs 0) (hLCis 0)
    have h1 := hfactor (Glow 1) (Clow 1) (fun _ h => Or.inl (Or.inr h))
      (hLCs 1) (hLCis 1)
    have hu := hfactor Gup Kup (fun _ h => Or.inr h) hUCs hUCis
    change Gup (Glow 1 (Glow 0 y)) = y ∧
      (Glow 0).symm ((Glow 1).symm (Gup.symm y)) = y
    rw [h0.1, h1.1, hu.1, hu.2, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  refine ⟨Tlow, lambdaLow, Nlow, Tup, lambdaUp, Nup, G, K, ?_, hUpositive,
    (hUwidth.trans_le hetatau), hUs, hUT, hUTi, hUH, hUNb, hUNsource, hUNtarget,
    hUNpoint, hUNinv, ?_, hLowdis.mono (hLcontain 0) (hLcontain 1), ?_,
    hImage, ?_, hFix, hK, hKsub, ?_, ?_,
    IsCollarEmbedding.postcompose_diffeomorph hpsi G⟩
  · intro i
    exact ⟨hLpositive i, (hLwidth i).trans_le hetatau, hLs i, hLT i, hLTi i,
      hLH i, hLNb i, hLNsource i, hLNtarget i, hLNpoint i, hLNinv i,
      fun y hy => (show |H y - W.level| < eta from hLband i hy).trans_le hetatau⟩
  · exact fun y hy => (show |H y - z| < eta from hUband hy).trans_le hetatau
  · intro i
    apply disjoint_left.mpr
    intro y hylo hyup
    have hlo := hLowerHeight i y hylo
    have hb : |H y - z| < eta := hUband hyup
    have hup := (abs_lt.mp hb).1
    linarith
  · rw [← hImage]
    exact G.symm_image_image S
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hnot
    exact hy (sub_eq_zero.mpr (hOutside y hnot).1)
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hnot
    exact hy (sub_eq_zero.mpr (hOutside y hnot).2)

end PoincareConjecture.M25.Topology3D
