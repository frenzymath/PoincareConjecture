import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedLowerEndGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NorthCapEndTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapHeightCompression
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_nonnested_lower_end_replacement
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (P : SurgeryCapProfile) (tau : ℝ) (htau : 0 < tau) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S : Set E3 := range j
    let R : Set E3 := S ∩ {y : E3 | W.level ≤ H y}
    let E : Fin 2 → Set E3 := fun i => j ''
      ((D.cap (W.label i)).sourceCap ∪ W.leg i '' (univ ×ˢ Icc
        ((D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal) W.level))
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    ∃ (T : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
      (lambda : Fin 2 → ℝ) (A N : Fin 2 → BallNeighborhoodChart E3 E3)
      (G : Fin 2 → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (C : Fin 2 → Set E3),
    let north : Fin 2 → Set E3 := fun i =>
      (fun q : UnitTwoSphere => T i ((P.model q).1, W.level + lambda i * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let south : Fin 2 → Set E3 := fun i =>
      (fun q : UnitTwoSphere => T i ((P.model q).1, W.level + lambda i * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let other : Fin 2 → Fin 2 := ![1, 0]
    (∀ i : Fin 2,
      0 < lambda i ∧ lambda i * P.heightBound < tau ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
      ContDiffOn ℝ ∞ (T i) (T i).source ∧
      ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
      (∀ p ∈ (T i).source, H (T i p) = p.2) ∧
      (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 0 →
        T i (((D.cap (W.label i)).profile.model q).1,
          (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal +
            (D.cap (W.label i)).scale * ((D.cap (W.label i)).profile.model q).2) =
          j ((D.cap (W.label i)).sourceChart q)) ∧
      (A i).boundary = E i ∪ north i ∧
      (N i).boundary = south i ∪ north i ∧
      (N i).chart.source = {y : E3 |
        ((M (heightCoordinates y)).1,
          W.level + lambda i * (M (heightCoordinates y)).2) ∈ (T i).source} ∧
      (N i).chart.target = (T i).target ∧
      (∀ y : E3, (N i).chart y = T i ((M (heightCoordinates y)).1,
        W.level + lambda i * (M (heightCoordinates y)).2)) ∧
      (∀ y : E3, (N i).chart.symm y = heightCoordinates.symm
        (M.symm (((T i).symm y).1, (((T i).symm y).2 - W.level) / lambda i))) ∧
      (A i).closedRegion ∩ {y : E3 | H y = W.level} =
        (fun x : E2 => (heightPlaneCoordinates u).symm (x, W.level)) ''
          (W.disc i).closedRegion ∧
      (N i).closedRegion ⊆ (A i).closedRegion ∧
      (N i).closedRegion ⊆ {y : E3 | |H y - W.level| < tau} ∧
      Disjoint (A i).inside S ∧
      (A i).closedRegion ∩ (R ∪ E (other i)) ⊆ north i ∧
      G i '' E i = south i ∧ (G i).symm '' south i = E i ∧
      (∀ y ∈ north i ∪ R ∪ (A (other i)).closedRegion,
        G i y = y ∧ (G i).symm y = y) ∧
      IsCompact (C i) ∧
      C i ⊆ (north i ∪ R ∪ (A (other i)).closedRegion)ᶜ ∧
      tsupport (fun y => G i y - y) ⊆ C i ∧
      tsupport (fun y => (G i).symm y - y) ⊆ C i) ∧
    Disjoint (A 0).closedRegion (A 1).closedRegion ∧
    let Gtotal := (G 0).trans (G 1)
    Gtotal '' S = R ∪ south 0 ∪ south 1 ∧
    Gtotal.symm '' (R ∪ south 0 ∪ south 1) = S ∧
    (∀ y ∈ R, Gtotal y = y ∧ Gtotal.symm y = y) ∧
    IsCollarEmbedding (fun p => Gtotal (psi p)) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S : Set E3 := range j
  let R : Set E3 := S ∩ {y : E3 | W.level ≤ H y}
  let ell : Fin 2 → ℝ := fun i =>
    (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal
  let E : Fin 2 → Set E3 := fun i => j ''
    ((D.cap (W.label i)).sourceCap ∪ W.leg i '' (univ ×ˢ Icc (ell i) W.level))
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  obtain ⟨T, lambda, o, A, hA, hdis, hS, hR⟩ :=
    exists_saddle_nonnested_lower_end_geometry hP psi hpsi u D W hnonnested P tau htau
  change S = R ∪ E 0 ∪ E 1 at hS
  let north : Fin 2 → Set E3 := fun i =>
    (fun q : UnitTwoSphere => T i ((P.model q).1, W.level + lambda i * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let south : Fin 2 → Set E3 := fun i =>
    (fun q : UnitTwoSphere => T i ((P.model q).1, W.level + lambda i * (P.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let other : Fin 2 → Fin 2 := ![1, 0]
  have hdisother (i : Fin 2) : Disjoint (A i).closedRegion (A (other i)).closedRegion := by
    fin_cases i
    · exact hdis
    · exact hdis.symm
  have hNs (i : Fin 2) : ∃ N : BallNeighborhoodChart E3 E3,
      N.boundary = south i ∪ north i ∧
      N.chart.source = {y : E3 | ((M (heightCoordinates y)).1,
        W.level + lambda i * (M (heightCoordinates y)).2) ∈ (T i).source} ∧
      N.chart.target = (T i).target ∧
      (∀ y : E3, N.chart y = T i ((M (heightCoordinates y)).1,
        W.level + lambda i * (M (heightCoordinates y)).2)) ∧
      (∀ y : E3, N.chart.symm y = heightCoordinates.symm
        (M.symm (((T i).symm y).1, (((T i).symm y).2 - W.level) / lambda i))) ∧
      N.closedRegion ⊆ (A i).closedRegion ∧
      N.closedRegion ⊆ {y : E3 | |H y - W.level| < tau} ∧
      north i = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} ∧
      south i ∩ north i = T i '' (sphere (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) := by
    obtain ⟨hl, hlt, hlg, hs, hT, hTi, hh, hold, hb, hcut,
      hfill, ho, ho1, hpatch, havoid, hret, hrim⟩ := hA i
    apply exists_saddle_contained_profile_ball P u (T i) hs hT hTi hh
      (A i) (ell i) W.level (lambda i) tau hl hlg hlt hfill
    intro y hy
    rw [← (A i).inside_union_boundary]
    exact Or.inr (hb.symm ▸ Or.inr hy)
  choose N hNb hNsource hNtarget hNpoint hNinv hNcontain hNshort hNcap hNrim using hNs
  have hGexists (i : Fin 2) :
      ∃ (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (C : Set E3),
        G '' E i = south i ∧ G.symm '' south i = E i ∧
        (∀ y ∈ north i ∪ R ∪ (A (other i)).closedRegion,
          G y = y ∧ G.symm y = y) ∧
        IsCompact C ∧ C ⊆ (north i ∪ R ∪ (A (other i)).closedRegion)ᶜ ∧
        tsupport (fun y => G y - y) ⊆ C ∧
        tsupport (fun y => G.symm y - y) ⊆ C := by
    obtain ⟨hl, hlt, hlg, hs, hT, hTi, hh, hold, hb, hcut,
      hfill, ho, ho1, hpatch, havoid, hret, hrim⟩ := hA i
    let K := R ∪ (A (other i)).closedRegion
    have hK : IsClosed K := hR.isClosed.union (A (other i)).closedRegion_compact.isClosed
    have hp : ∀ q : UnitTwoSphere, -o i < (heightCoordinates (q : E3)).2 →
        (N i).chart (q : E3) ∈ (A i).boundary := by
      intro q hq
      rw [hNpoint]
      exact hpatch q hq
    have hAn : (A i).boundary = E i ∪ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      exact hb
    have hNn : (N i).boundary = south i ∪ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      exact hNb i
    have hmeet : E i ∩ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} =
        south i ∩ (N i).chart ''
          {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      exact hrim.trans (hNrim i).symm
    have hAK : (A i).closedRegion ∩ K ⊆ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNcap i]
      rintro y ⟨hyA, hyR | hyO⟩
      · exact hret ⟨hyA, Or.inl hyR⟩
      · exact False.elim (Set.disjoint_left.mp (hdisother i) hyA hyO)
    simpa only [← hNcap i, K, union_assoc] using
      exists_saddle_north_cap_end_transport (A i) (N i) (o i) ho ho1 hp
        (hNcontain i) (E i) (south i) K hK hAn hNn hmeet hAK
  choose G C hGe hGinv hGfix hC hCsub hCsupp hCisupp using hGexists
  have hEclosed (i : Fin 2) : E i ⊆ (A i).closedRegion := by
    intro y hy
    rw [← (A i).inside_union_boundary]
    apply Or.inr
    rw [(hA i).2.2.2.2.2.2.2.2.1]
    exact Or.inl hy
  have hSouthclosed (i : Fin 2) : south i ⊆ (A i).closedRegion := by
    intro y hy
    apply hNcontain i
    rw [← (N i).inside_union_boundary, hNb i]
    exact Or.inr (Or.inl hy)
  have hfixedImage (i : Fin 2) (X : Set E3)
      (hX : X ⊆ north i ∪ R ∪ (A (other i)).closedRegion) : G i '' X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [(hGfix i x (hX hx)).1] using hx
    · intro hy
      exact ⟨y, hy, (hGfix i y (hX hy)).1⟩
  have hGR (i : Fin 2) : G i '' R = R :=
    hfixedImage i R (fun _ hy => Or.inl (Or.inr hy))
  have hG0E1 : G 0 '' E 1 = E 1 := by
    apply hfixedImage 0
    intro y hy
    apply Or.inr
    simpa only [other, Matrix.cons_val_zero] using hEclosed 1 hy
  have hG1south0 : G 1 '' south 0 = south 0 := by
    apply hfixedImage 1
    intro y hy
    apply Or.inr
    simpa only [other, Matrix.cons_val_one, Matrix.cons_val_zero] using hSouthclosed 0 hy
  let Gtotal := (G 0).trans (G 1)
  have hG0S : G 0 '' S = R ∪ south 0 ∪ E 1 := by
    rw [hS, image_union, image_union, hGR 0, hGe 0, hG0E1]
  have htotal : Gtotal '' S = R ∪ south 0 ∪ south 1 := by
    calc
      Gtotal '' S = G 1 '' (G 0 '' S) := by
        rw [image_image]
        rfl
      _ = G 1 '' (R ∪ south 0 ∪ E 1) := congrArg (fun X => G 1 '' X) hG0S
      _ = R ∪ south 0 ∪ south 1 := by
        rw [image_union, image_union, hGR 1, hG1south0, hGe 1]
  refine ⟨T, lambda, A, N, G, C, ?_, hdis, htotal, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hl, hlt, hlg, hs, hT, hTi, hh, hold, hb, hcut,
      hfill, ho, ho1, hpatch, havoid, hret, hrim⟩ := hA i
    exact ⟨hl, hlt, hs, hT, hTi, hh, hold, hb, hNb i, hNsource i,
      hNtarget i, hNpoint i, hNinv i, hcut, hNcontain i, hNshort i,
      havoid, hret, hGe i, hGinv i, hGfix i, hC i, hCsub i, hCsupp i, hCisupp i⟩
  · change Gtotal.symm '' (R ∪ south 0 ∪ south 1) = S
    rw [← htotal]
    exact Gtotal.symm_image_image S
  · intro y hy
    have h0 := hGfix 0 y (Or.inl (Or.inr hy))
    have h1 := hGfix 1 y (Or.inl (Or.inr hy))
    change G 1 (G 0 y) = y ∧ (G 0).symm ((G 1).symm y) = y
    rw [h0.1, h1.1, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  · exact IsCollarEmbedding.postcompose_diffeomorph hpsi Gtotal

end PoincareConjecture.M25.Topology3D
