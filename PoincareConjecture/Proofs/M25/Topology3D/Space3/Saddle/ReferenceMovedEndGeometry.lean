import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceCutMotion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceFixedEndGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceLowerLabelImages
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlatCapBall
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_nonnested_reference_moved_end_geometry
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (P : SurgeryCapProfile)
    (m p tau : ℝ) (hm : m ∈ Ioo (-1 / 4 : ℝ) 0)
    (hp : p ∈ Ioo (0 : ℝ) 2) (htau : 0 < tau) :
    let L := heightPlaneCoordinates u
    let F : E3 → E3 := fun y =>
      L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
        (nonnestedReferenceDiffeomorph 0 d hd y).2)
    let j : UnitTwoSphere → E3 := fun q => F (q : E3)
    let psi : UnitTwoSphere × ℝ → E3 := fun q => F ((1 + q.2) • (q.1 : E3))
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range j
    let cut : Fin 3 → ℝ := ![m, m, p]
    let sign : Fin 3 → ℝ := ![1, 1, -1]
    let E : Fin 3 → Set E3 := ![
      j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ m},
      j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ m},
      j '' {q | p ≤ H (j q)}]
    let R := S ∩ {y | m ≤ H y ∧ H y ≤ p}
    let sector : Fin 3 → Set E3 := ![
      {y | 0 < (J2 (L y).1).2}, {y | (J2 (L y).1).2 < 0}, univ]
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    IsCollarEmbedding psi ∧
    ∃ (b : ℝ) (T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3),
      0 < b ∧ b < tau ∧ b < min (-m) p ∧ b < 1 / 256 ∧
      (∀ i : Fin 3,
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
        ContDiffOn ℝ ∞ (T i) (T i).source ∧
        ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
        (∀ x ∈ (T i).source, H (T i x) = x.2) ∧
        (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) ∧
        ∀ z : ℝ, |z - cut i| < b →
          T i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
            S ∩ {y | H y = z} ∩ sector i) ∧
      ∀ lambda : Fin 3 → ℝ, (∀ i, 0 < lambda i) →
        (∀ i, lambda i * P.heightBound < b) →
        ∃ (A N : Fin 3 → BallNeighborhoodChart E3 E3) (o : Fin 3 → ℝ),
          let cap : Fin 3 → E3 → E3 := fun i y =>
            T i ((M (heightCoordinates y)).1,
              cut i + sign i * lambda i * (M (heightCoordinates y)).2)
          let north : Fin 3 → Set E3 := fun i => cap i ''
            {y | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
          let south : Fin 3 → Set E3 := fun i => cap i ''
            {y | ‖y‖ = 1 ∧ (heightCoordinates y).2 ≤ 0}
          (∀ i : Fin 3,
            (A i).boundary = E i ∪ north i ∧
            (A i).closedRegion ⊆ F '' closedBall (0 : E3) 1 ∧
            Disjoint (A i).inside S ∧
            (A i).closedRegion ∩ R ⊆ north i ∧
            E i ∩ north i = T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) ∧
            south i ∩ north i = T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) ∧
            (∀ s ∈ Icc (0 : ℝ) b,
              let z := cut i - sign i * s
              (A i).inside ∩ {y | H y = z} =
                T i '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
              (A i).closedRegion ∩ {y | H y = z} =
                T i '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) ∧
            (N i).boundary = south i ∪ north i ∧
            (N i).chart.source = {y : E3 |
              ((M (heightCoordinates y)).1,
                cut i + sign i * lambda i * (M (heightCoordinates y)).2) ∈ (T i).source} ∧
            (N i).chart.target = (T i).target ∧
            (∀ y : E3, (N i).chart y = cap i y) ∧
            (∀ y : E3, (N i).chart.symm y = heightCoordinates.symm
              (M.symm (((T i).symm y).1,
                (((T i).symm y).2 - cut i) / (sign i * lambda i)))) ∧
            (N i).closedRegion ⊆ (A i).closedRegion ∧
            (N i).closedRegion ⊆ {y | |H y - cut i| ≤ lambda i * P.heightBound} ∧
            (N i).closedRegion ⊆ {y | |H y - cut i| < tau} ∧
            0 < o i ∧ o i < 1 / 4 ∧
            (∀ q : UnitTwoSphere, -o i < (heightCoordinates (q : E3)).2 →
              (N i).chart (q : E3) ∈ (A i).boundary)) ∧
          (∀ i k : Fin 3, i ≠ k → Disjoint (A i).closedRegion (A k).closedRegion) ∧
          S = R ∪ (⋃ i : Fin 3, E i) := by
  classical
  let L := heightPlaneCoordinates u
  let F : E3 → E3 := fun y =>
    L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
      (nonnestedReferenceDiffeomorph 0 d hd y).2)
  let j : UnitTwoSphere → E3 := fun q => F (q : E3)
  let psi : UnitTwoSphere × ℝ → E3 := fun q => F ((1 + q.2) • (q.1 : E3))
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S := range j
  let old : Fin 3 → ℝ := ![-1 / 8, -1 / 8, 3 / 2]
  let cut : Fin 3 → ℝ := ![m, m, p]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  let Eold : Fin 3 → Set E3 := ![
    j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ -1 / 8},
    j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ -1 / 8},
    j '' {q | 3 / 2 ≤ H (j q)}]
  let E : Fin 3 → Set E3 := ![
    j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ m},
    j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ m},
    j '' {q | p ≤ H (j q)}]
  let Rold := S ∩ {y | -1 / 8 ≤ H y ∧ H y ≤ 3 / 2}
  let R := S ∩ {y | m ≤ H y ∧ H y ≤ p}
  let sector : Fin 3 → Set E3 := ![
    {y | 0 < (J2 (L y).1).2}, {y | (J2 (L y).1).2 < 0}, univ]
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  obtain ⟨hpsi, radius, width, Phi, gPart, KPart, CPart, b, etaFix,
    hPart, _hDisjoint, hb, hbTau, hbCuts, hbOld, hbWidth, hetaFix, hFixedSlab,
    _hCompact, _hg, _hgi, hK, _hKi, hMono, _hgZero, hKZero, hHeight,
    hMem, hImage, hgFixed, _hKFixed, _hSupport, _hSlab, hAffine,
    hLevels, hMiddle, _hMiddleInv, hRegion⟩ :=
    exists_nonnested_reference_cut_motion sigma hsigma hsigmaSmall d hd
      hdNear hdZero hdBounds hdDeriv J2 hJ2 u m p tau hm hp htau
  let gf := fun r : ℝ => (gPart 0 r).trans (gPart 1 r)
  let Kf := fun r : ℝ => (KPart 0 r).trans (KPart 1 r)
  let g := gf 1
  let K := Kf 1
  change K '' Rold = R at hMiddle
  have hg0 (r : ℝ) : gf r 0 = 0 := by
    apply (hgFixed r 0 ?_).1
    intro hz
    have hout := hFixedSlab (show (0 : ℝ) ∈ Icc (-etaFix) etaFix by
      constructor <;> linarith)
    apply hout
    rcases hz with hz | hz
    · exact Or.inl ((hPart 0).2.2.2.2.2.2.2.2.2.1 hz)
    · exact Or.inr ((hPart 1).2.2.2.2.2.2.2.2.2.1 hz)
  obtain ⟨_hSign, hLabels⟩ := nonnested_reference_lower_label_images d hd
    (fun q hq => (hdBounds q hq).1) J2 u Kf gf hK
    (fun y => (hKZero y).1) (fun r y => (hMem r y).1)
    (fun r y => (hHeight r y).1) (fun r => (hMono r).1) hg0
  have hAff (i : Fin 3) (h : ℝ) (hh : |h| ≤ b) :
      g (old i + h) = cut i + h ∧ g.symm (cut i + h) = old i + h := by
    fin_cases i
    · exact hAffine 0 h (hh.trans (hbWidth 0).le)
    · exact hAffine 0 h (hh.trans (hbWidth 0).le)
    · exact hAffine 1 h (hh.trans (hbWidth 1).le)
  have hAnchor (i : Fin 3) : g (old i) = cut i := by
    simpa only [add_zero] using (hAff i 0 (by simpa using hb.le)).1
  have hsg (i : Fin 3) : |sign i| = 1 := by fin_cases i <;> norm_num [sign]
  have hjp (q : UnitTwoSphere) :
      J2 (L (j q)).1 = ((q : E3) 0 / Real.sqrt 2, (q : E3) 1 / Real.sqrt 2) := by
    change J2 (L (L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd q).1,
      (nonnestedReferenceDiffeomorph 0 d hd q).2))).1 = _
    rw [L.apply_symm_apply, J2.apply_symm_apply,
      (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hshape (eps z : ℝ) :
      j '' {q : UnitTwoSphere | 0 < eps * (q : E3) 1 ∧ H (j q) = z} =
        S ∩ {y | H y = z} ∩ {y | 0 < eps * (J2 (L y).1).2} := by
    ext y
    constructor
    · rintro ⟨q, ⟨hq, hz⟩, rfl⟩
      refine ⟨⟨⟨q, rfl⟩, hz⟩, ?_⟩
      change 0 < eps * (J2 (L (j q)).1).2
      rw [hjp, ← mul_div_assoc]
      exact (div_pos_iff_of_pos_right htwo).2 hq
    · rintro ⟨⟨⟨q, rfl⟩, hz⟩, hq⟩
      refine ⟨q, ⟨?_, hz⟩, rfl⟩
      change 0 < eps * (J2 (L (j q)).1).2 at hq
      rw [hjp, ← mul_div_assoc] at hq
      exact (div_pos_iff_of_pos_right htwo).1 hq
  have hCircleMove (i : Fin 3) (z : ℝ) (hz : |z - old i| < b) :
      K '' (S ∩ {y | H y = z} ∩ sector i) =
        S ∩ {y | H y = g z} ∩ sector i := by
    fin_cases i
    · have hzneg : z < 0 := by
        have hh := (abs_lt.mp hz).2
        norm_num [old] at hh
        linarith
      have hh := (hLabels 1 1 z one_ne_zero hzneg).2.2.1
      change K '' (j '' {q | 0 < 1 * (q : E3) 1 ∧ H (j q) = z}) =
        j '' {q | 0 < 1 * (q : E3) 1 ∧ H (j q) = g z} at hh
      rw [hshape 1 z, hshape 1 (g z)] at hh
      change K '' (S ∩ {y | H y = z} ∩ {y | 0 < (J2 (L y).1).2}) =
        S ∩ {y | H y = g z} ∩ {y | 0 < (J2 (L y).1).2}
      simpa only [one_mul] using hh
    · have hzneg : z < 0 := by
        have hh := (abs_lt.mp hz).2
        norm_num [old] at hh
        linarith
      have hh := (hLabels 1 (-1) z (by norm_num) hzneg).2.2.1
      change K '' (j '' {q | 0 < -1 * (q : E3) 1 ∧ H (j q) = z}) =
        j '' {q | 0 < -1 * (q : E3) 1 ∧ H (j q) = g z} at hh
      rw [hshape (-1) z, hshape (-1) (g z)] at hh
      change K '' (S ∩ {y | H y = z} ∩ {y | (J2 (L y).1).2 < 0}) =
        S ∩ {y | H y = g z} ∩ {y | (J2 (L y).1).2 < 0}
      simpa only [neg_one_mul, neg_pos] using hh
    · change K '' (S ∩ {y | H y = z} ∩ univ) = S ∩ {y | H y = g z} ∩ univ
      simpa only [inter_univ] using (hLevels 1 z).1
  have hPred (f : ℝ → Prop) :
      j '' {q | f (H (j q))} = S ∩ {y | f (H y)} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, rfl⟩, hq⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      exact ⟨q, hq, rfl⟩
  have hE (i : Fin 3) : K '' Eold i = E i := by
    fin_cases i
    · change K '' (j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ -1 / 8}) =
        j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ m}
      have hh := (hLabels 1 1 (-1 / 8) one_ne_zero (by norm_num)).1
      change K '' (j '' {q | 0 < 1 * (q : E3) 1 ∧ H (j q) ≤ -1 / 8}) =
        j '' {q | 0 < 1 * (q : E3) 1 ∧ H (j q) ≤ g (-1 / 8)} at hh
      simpa only [one_mul, show g (-1 / 8) = m from hAnchor 0] using hh
    · change K '' (j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ -1 / 8}) =
        j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ m}
      have hh := (hLabels 1 (-1) (-1 / 8) (by norm_num) (by norm_num)).1
      change K '' (j '' {q | 0 < -1 * (q : E3) 1 ∧ H (j q) ≤ -1 / 8}) =
        j '' {q | 0 < -1 * (q : E3) 1 ∧ H (j q) ≤ g (-1 / 8)} at hh
      simpa only [neg_one_mul, neg_pos, show g (-1 / 8) = m from hAnchor 0] using hh
    · change K '' (j '' {q | 3 / 2 ≤ H (j q)}) = j '' {q | p ≤ H (j q)}
      rw [hPred, hPred]
      have hh : K '' (S ∩ {y | 3 / 2 ≤ H y}) = S ∩ {y | g (3 / 2) ≤ H y} :=
        (hLevels 1 (3 / 2)).2.2.2.2.1
      simpa only [show g (3 / 2) = p from hAnchor 2] using hh
  obtain ⟨Told, hTold, hLater⟩ := exists_nonnested_reference_fixed_end_geometry
    sigma hsigma hsigmaSmall d hd hdZero hdBounds J2 hJ2 u P
  let T := fun i => heightTransportTube (Told i) g K
  have hSlice (i : Fin 3) (X : Set E2) (z : ℝ) :
      K '' (Told i '' (X ×ˢ ({z} : Set ℝ))) =
        T i '' (X ×ˢ ({g z} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩, rfl⟩
      have hw' : w = z := hw
      subst w
      exact ⟨(x, g z), ⟨hx, rfl⟩,
        heightTransportTube_reparametrized_apply (Told i) g K (x, z)⟩
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      have hw' : w = g z := hw
      subst w
      exact ⟨Told i (x, z), ⟨(x, z), ⟨hx, rfl⟩, rfl⟩,
        (heightTransportTube_reparametrized_apply (Told i) g K (x, z)).symm⟩
  have hTube (i : Fin 3) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
      ContDiffOn ℝ ∞ (T i) (T i).source ∧
      ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
      (∀ x ∈ (T i).source, H (T i x) = x.2) ∧
      (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) ∧
      ∀ z : ℝ, |z - cut i| < b →
        T i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
          S ∩ {y | H y = z} ∩ sector i := by
    obtain ⟨hsrc, hsm, hsi, hh, hhi, hc⟩ := hTold i
    refine ⟨heightTransportTube_closedDisc_source _ _ _ hsrc,
      heightTransportTube_contDiffOn _ _ _ hsm,
      heightTransportTube_contDiffOn_symm _ _ _ hsi, ?_, ?_, ?_⟩
    · intro x hx
      exact heightTransportTube_height (Told i) g K u u hh
        (fun y => (hHeight 1 y).1) x hx
    · intro y hy
      change g (((Told i).symm (K.symm y)).2) = H y
      rw [hhi _ ((heightTransportTube_mem_target _ _ _ y).1 hy),
        (hHeight 1 y).2, g.apply_symm_apply]
    · intro z hz
      let zold := old i + (z - cut i)
      have hzo : |zold - old i| < b := by simpa [zold] using hz
      have hgz : g zold = z := by
        simpa only [add_sub_cancel] using (hAff i (z - cut i) hz.le).1
      calc
        _ = K '' (Told i '' (sphere 0 1 ×ˢ ({zold} : Set ℝ))) := by
          rw [hSlice, hgz]
        _ = K '' (S ∩ {y | H y = zold} ∩ sector i) := by
          rw [hc zold (hzo.trans (by linarith))]
        _ = S ∩ {y | H y = z} ∩ sector i := by rw [hCircleMove i zold hzo, hgz]
  refine ⟨hpsi, b, T, hb, hbTau, hbCuts, hbOld, hTube, ?_⟩
  intro lambda hlambda hsmall
  obtain ⟨Aold, Nold, o, hOld, hOldDisjoint, hOldCover⟩ :=
    hLater lambda hlambda (fun i => (hsmall i).trans hbOld)
  let capOld : Fin 3 → E3 → E3 := fun i y =>
    Told i ((M (heightCoordinates y)).1,
      old i + sign i * lambda i * (M (heightCoordinates y)).2)
  let northOld := fun i => capOld i '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  let southOld := fun i => capOld i '' {y : E3 | ‖y‖ = 1 ∧ (heightCoordinates y).2 ≤ 0}
  let cap : Fin 3 → E3 → E3 := fun i y =>
    T i ((M (heightCoordinates y)).1,
      cut i + sign i * lambda i * (M (heightCoordinates y)).2)
  let north := fun i => cap i '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  let south := fun i => cap i '' {y : E3 | ‖y‖ = 1 ∧ (heightCoordinates y).2 ≤ 0}
  let A := fun i => (Aold i).mapDiffeomorph K
  let J := heightCoordinates.toDiffeomorph.trans M
  have hnonzero (i : Fin 3) : sign i * lambda i ≠ 0 := by
    apply mul_ne_zero _ (hlambda i).ne'
    intro hz
    have hh := hsg i
    rw [hz, abs_zero] at hh
    norm_num at hh
  let B : Fin 3 → Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ :=
    fun i => {
      toEquiv := {
        toFun := fun v => (v.1, cut i + sign i * lambda i * v.2)
        invFun := fun v => (v.1, (v.2 - cut i) / (sign i * lambda i))
        left_inv := by
          rintro ⟨x, z⟩
          apply Prod.ext
          · rfl
          change (cut i + sign i * lambda i * z - cut i) / (sign i * lambda i) = z
          field_simp [(mul_ne_zero_iff.mp (hnonzero i)).1, (hlambda i).ne']
          ring
        right_inv := by
          rintro ⟨x, z⟩
          apply Prod.ext
          · rfl
          change cut i + sign i * lambda i * ((z - cut i) / (sign i * lambda i)) = z
          field_simp [(mul_ne_zero_iff.mp (hnonzero i)).1, (hlambda i).ne']
          ring }
      contMDiff_toFun := (by
        fun_prop : ContDiff ℝ ∞
          (fun v : E2 × ℝ => (v.1, cut i + sign i * lambda i * v.2))).contMDiff
      contMDiff_invFun := (by
        fun_prop : ContDiff ℝ ∞
          (fun v : E2 × ℝ => (v.1, (v.2 - cut i) / (sign i * lambda i)))).contMDiff }
  let Q := fun i => J.trans (B i)
  have hhor (y : E3) (hy : y ∈ closedBall (0 : E3) 1) : ‖(J y).1‖ ≤ 1 := by
    apply flatCapDiffeomorph_fst_norm_le P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound
    change ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 ≤ 1
    rw [← heightCoordinates_norm_sq]
    have hyn := mem_closedBall_zero_iff.mp hy
    nlinarith [norm_nonneg y]
  have hQs (i : Fin 3) (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      Q i y ∈ (T i).source :=
    (hTube i).1 ⟨mem_closedBall_zero_iff.mpr (hhor y hy), mem_univ _⟩
  let N : Fin 3 → BallNeighborhoodChart E3 E3 := fun i => {
    chart := (Q i).toHomeomorph.toOpenPartialHomeomorph.trans (T i)
    closedBall_subset_source := fun y hy => ⟨mem_univ y, hQs i y hy⟩
    smooth := (hTube i).2.1.comp (Q i).contDiff.contDiffOn (fun _ hx => hx.2)
    smooth_symm := (Q i).symm.contDiff.comp_contDiffOn
      ((hTube i).2.2.1.mono (fun _ hy => hy.1)) }
  have hNpoint (i : Fin 3) (y : E3) : (N i).chart y = cap i y := rfl
  have hNsource (i : Fin 3) : (N i).chart.source = {y : E3 |
      ((M (heightCoordinates y)).1,
        cut i + sign i * lambda i * (M (heightCoordinates y)).2) ∈ (T i).source} := by
    ext y
    change (y ∈ (univ : Set E3) ∧ Q i y ∈ (T i).source) ↔ Q i y ∈ (T i).source
    simp only [mem_univ, true_and]
  have hNtarget (i : Fin 3) : (N i).chart.target = (T i).target := by
    ext y
    change (y ∈ (T i).target ∧ (T i).symm y ∈ (univ : Set (E2 × ℝ))) ↔ y ∈ (T i).target
    simp only [mem_univ, and_true]
  have hNinv (i : Fin 3) (y : E3) : (N i).chart.symm y = heightCoordinates.symm
      (M.symm (((T i).symm y).1, (((T i).symm y).2 - cut i) / (sign i * lambda i))) := rfl
  have hHeightSet (U : Set E3) (z : ℝ) :
      K '' (U ∩ {y | H y = z}) = (K '' U) ∩ {y | H y = g z} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hz⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (hHeight 1 x).1.trans (congrArg g hz)⟩
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      apply g.injective
      exact (hHeight 1 x).1.symm.trans hz
  refine ⟨A, N, o, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hAbOld, hAcOld, hAvoidOld, hCoreOld, hRimOld, hCutsOld,
      hNbOld, hNsOld, _hNtOld, hNpOld, _hNiOld, hNcOld, hNhOld,
      ho, hoSmall, hPatchOld⟩ := hOld i
    have hOldHeight (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
        H ((Nold i).chart y) = old i + sign i * lambda i * (J y).2 := by
      rw [hNpOld]
      apply (hTold i).2.2.2.1
      have hh := (Nold i).closedBall_subset_source hy
      rw [hNsOld] at hh
      exact hh
    have hOffset (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
        |sign i * lambda i * (J y).2| ≤ b := by
      have hh := hNhOld ⟨y, hy, rfl⟩
      change |H ((Nold i).chart y) - old i| ≤ lambda i * P.heightBound at hh
      rw [hOldHeight y hy, add_sub_cancel_left] at hh
      exact hh.trans (hsmall i).le
    have hEq (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
        (N i).chart y = K ((Nold i).chart y) := by
      rw [hNpoint, hNpOld]
      change K (Told i ((J y).1, g.symm (cut i + sign i * lambda i * (J y).2))) =
        K (Told i ((J y).1, old i + sign i * lambda i * (J y).2))
      rw [(hAff i _ (hOffset y hy)).2]
    have hImg (X : Set E3) (hX : X ⊆ closedBall (0 : E3) 1) :
        (N i).chart '' X = K '' ((Nold i).chart '' X) := by
      calc
        _ = (fun y => K ((Nold i).chart y)) '' X := image_congr (fun y hy => hEq y (hX hy))
        _ = _ := (image_image K (Nold i).chart X).symm
    have hCapImg (X : Set E3) (hX : X ⊆ closedBall (0 : E3) 1) :
        cap i '' X = K '' (capOld i '' X) := by
      simpa only [hNpoint, hNpOld] using hImg X hX
    have hNorth : north i = K '' northOld i :=
      hCapImg _ (fun y hy => mem_closedBall_zero_iff.mpr hy.1.le)
    have hSouth : south i = K '' southOld i :=
      hCapImg _ (fun y hy => mem_closedBall_zero_iff.mpr hy.1.le)
    have hNc : (N i).closedRegion = K '' (Nold i).closedRegion := hImg _ (Subset.rfl)
    have hAb : (A i).boundary = E i ∪ north i := by
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary, hAbOld, image_union]
      rw [hE i, ← hNorth]
    have hAc : (A i).closedRegion ⊆ F '' closedBall (0 : E3) 1 := by
      rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion, ← (hRegion 1).2.1]
      exact image_mono hAcOld
    have hAvoid : Disjoint (A i).inside S := by
      rw [BallNeighborhoodChart.mapDiffeomorph_inside]
      apply Set.disjoint_left.mpr
      rintro y ⟨x, hx, rfl⟩ hy
      exact Set.disjoint_left.mp hAvoidOld hx ((hMem 1 x).1.mp hy)
    have hCore : (A i).closedRegion ∩ R ⊆ north i := by
      rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion, ← hMiddle,
        ← Set.image_inter (f := (K : E3 → E3)) K.injective, hNorth]
      exact image_mono hCoreOld
    have hRim : E i ∩ north i =
        T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) := by
      rw [← hE i, hNorth, ← Set.image_inter (f := (K : E3 → E3)) K.injective,
        hRimOld, hSlice, hAnchor]
    have hCuts (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
        (A i).inside ∩ {y | H y = cut i - sign i * s} =
          T i '' (ball (0 : E2) 1 ×ˢ ({cut i - sign i * s} : Set ℝ)) ∧
        (A i).closedRegion ∩ {y | H y = cut i - sign i * s} =
          T i '' (closedBall (0 : E2) 1 ×ˢ ({cut i - sign i * s} : Set ℝ)) := by
      have hbound : |-sign i * s| ≤ b := by
        rw [abs_mul, abs_neg, hsg, one_mul, abs_of_nonneg hs.1]
        exact hs.2
      have hgz : g (old i - sign i * s) = cut i - sign i * s := by
        simpa only [neg_mul, ← sub_eq_add_neg] using (hAff i (-sign i * s) hbound).1
      obtain ⟨hci, hcc⟩ := hCutsOld s ⟨hs.1, hs.2.trans (by linarith)⟩
      constructor
      · rw [BallNeighborhoodChart.mapDiffeomorph_inside, ← hgz, ← hHeightSet, hci, hSlice]
      · rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion, ← hgz, ← hHeightSet, hcc, hSlice]
    have hNb : (N i).boundary = south i ∪ north i := by
      change (N i).chart '' sphere 0 1 = _
      rw [hImg _ sphere_subset_closedBall]
      change K '' (Nold i).boundary = _
      rw [hNbOld, image_union, ← hSouth, ← hNorth]
    have hContain : (N i).closedRegion ⊆ (A i).closedRegion := by
      rw [hNc, BallNeighborhoodChart.mapDiffeomorph_closedRegion]
      exact image_mono hNcOld
    have hNheight : (N i).closedRegion ⊆ {y | |H y - cut i| ≤ lambda i * P.heightBound} := by
      rintro y ⟨x, hx, rfl⟩
      have hh := hNhOld ⟨x, hx, rfl⟩
      change |H ((Nold i).chart x) - old i| ≤ lambda i * P.heightBound at hh
      change |H ((N i).chart x) - cut i| ≤ lambda i * P.heightBound
      rw [hEq x hx, (hHeight 1 _).1, hOldHeight x hx,
        (hAff i _ (hOffset x hx)).1, add_sub_cancel_left]
      simpa only [hOldHeight x hx, add_sub_cancel_left] using hh
    have hNear : (N i).closedRegion ⊆ {y | |H y - cut i| < tau} :=
      fun y hy => (hNheight hy).trans_lt ((hsmall i).trans hbTau)
    have hPatch (q : UnitTwoSphere) (hq : -o i < (heightCoordinates (q : E3)).2) :
        (N i).chart (q : E3) ∈ (A i).boundary := by
      rw [hEq q (sphere_subset_closedBall q.property),
        BallNeighborhoodChart.mapDiffeomorph_boundary]
      exact ⟨(Nold i).chart q, hPatchOld q hq, rfl⟩
    have hequator (y : E3) (hyn : ‖y‖ = 1) (hyh : (heightCoordinates y).2 = 0) :
        M (heightCoordinates y) = ((heightCoordinates y).1, 0) ∧
        ‖(heightCoordinates y).1‖ = 1 := by
      have ha : P.horizontal 0 = 1 := by simpa using P.horizontal_near 0 (by norm_num)
      refine ⟨?_, ?_⟩
      · rw [flatCapDiffeomorph_apply, hyh, ha, one_smul, mul_zero]
      · have hh := heightCoordinates_norm_sq y
        rw [hyn, hyh] at hh
        nlinarith [norm_nonneg (heightCoordinates y).1]
    have hMeet : south i ∩ north i =
        T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) := by
      ext y
      constructor
      · rintro ⟨⟨q, ⟨hqn, hqh⟩, hqy⟩, ⟨r, ⟨hrn, hrh⟩, hry⟩⟩
        have hqr : q = r := (N i).chart.injOn
          ((N i).closedBall_subset_source (mem_closedBall_zero_iff.mpr hqn.le))
          ((N i).closedBall_subset_source (mem_closedBall_zero_iff.mpr hrn.le))
          (hqy.trans hry.symm)
        subst r
        obtain ⟨hqM, hqNorm⟩ := hequator q hqn (le_antisymm hqh hrh)
        refine ⟨((heightCoordinates q).1, cut i),
          ⟨mem_sphere_zero_iff_norm.mpr hqNorm, rfl⟩, ?_⟩
        have hh : cap i q = T i ((heightCoordinates q).1, cut i) := by
          dsimp [cap]
          rw [hqM]
          simp only [mul_zero, add_zero]
        exact hh.symm.trans hqy
      · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
        have hz' : z = cut i := hz
        subst z
        have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
        let y := heightCoordinates.symm (x, (0 : ℝ))
        have hyn : ‖y‖ = 1 := by
          have hh := heightCoordinates_symm_norm_sq (x, (0 : ℝ))
          rw [hxn] at hh
          nlinarith [norm_nonneg y]
        have hyh : (heightCoordinates y).2 = 0 := by
          simp only [y, heightCoordinates.apply_symm_apply]
        have hcap : cap i y = T i (x, cut i) := by
          dsimp [cap]
          rw [(hequator y hyn hyh).1]
          simp only [y, heightCoordinates.apply_symm_apply, mul_zero, add_zero]
        exact ⟨⟨y, ⟨hyn, hyh.le⟩, hcap⟩, ⟨y, ⟨hyn, hyh.ge⟩, hcap⟩⟩
    exact ⟨hAb, hAc, hAvoid, hCore, hRim, hMeet, hCuts, hNb,
      hNsource i, hNtarget i, hNpoint i, hNinv i, hContain, hNheight, hNear,
      ho, hoSmall, hPatch⟩
  · intro i k hik
    rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion,
      BallNeighborhoodChart.mapDiffeomorph_closedRegion]
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz : x = z := K.injective (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (hOldDisjoint i k hik) hx (hxz.symm ▸ hz)
  · calc
      S = K '' S := (hImage 1).1.symm
      _ = K '' (Rold ∪ ⋃ i : Fin 3, Eold i) := congrArg (fun X => K '' X) hOldCover
      _ = R ∪ ⋃ i : Fin 3, E i := by rw [image_union, hMiddle, image_iUnion]; simp_rw [hE]

end PoincareConjecture.M25.Topology3D
