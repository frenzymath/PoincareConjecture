import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceScalarWindow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceCutConjugacy
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceLowerSlices
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceUpperRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarRadialCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_nonnested_reference_cut_motion
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (m p tau : ℝ)
    (hm : m ∈ Ioo (-1 / 4 : ℝ) 0) (hp : p ∈ Ioo (0 : ℝ) 2)
    (htau : 0 < tau) :
    let L := heightPlaneCoordinates u
    let F : E3 → E3 := fun y =>
      L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
        (nonnestedReferenceDiffeomorph 0 d hd y).2)
    let j : UnitTwoSphere → E3 := fun q => F (q : E3)
    let psi : UnitTwoSphere × ℝ → E3 := fun q => F ((1 + q.2) • (q.1 : E3))
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S : Set E3 := range j
    let old : Fin 2 → ℝ := ![-1 / 8, 3 / 2]
    let dest : Fin 2 → ℝ := ![m, p]
    let lo : Fin 2 → ℝ := ![-1 / 4, 0]
    let hi : Fin 2 → ℝ := ![0, 2]
    let left : Fin 2 → ℝ := fun i => min (old i) (dest i)
    let right : Fin 2 → ℝ := fun i => max (old i) (dest i)
    let center : Fin 2 → ℝ := fun i => (left i + right i) / 2
    IsCollarEmbedding psi ∧
    ∃ (radius width : Fin 2 → ℝ)
      (Phi : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (gPart : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (KPart : Fin 2 → ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (CPart : Fin 2 → Set ℝ) (b etaFix : ℝ),
      let V : Fin 2 → Set ℝ := fun i =>
        Ioo (left i - 3 * width i) (right i + 3 * width i)
      let g := fun r : ℝ => (gPart 0 r).trans (gPart 1 r)
      let K := fun r : ℝ => (KPart 0 r).trans (KPart 1 r)
      let C : Set ℝ := CPart 0 ∪ CPart 1
      (∀ i : Fin 2,
        0 < radius i ∧ 0 < width i ∧
        Icc (left i) (right i) ⊆
          Ioo (center i - radius i) (center i + radius i) ∧
        Icc (left i - 4 * width i) (right i + 4 * width i) ⊆
          Ioo (lo i) (hi i) ∩ Ioo (center i - radius i) (center i + radius i) ∧
        ContDiff ℝ ∞ (fun q : ℝ × E2 => Phi i q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × E2 => (Phi i q.1).symm q.2) ∧
        (∀ x : E2, Phi i (center i) x = x) ∧
        (∀ z ∈ Ioo (center i - radius i) (center i + radius i), ∀ x : E2,
          L.symm (Phi i z x, z) ∈ S ↔ L.symm (x, center i) ∈ S) ∧
        IsCompact (CPart i) ∧ CPart i ⊆ V i ∧
        ContDiff ℝ ∞ (fun q : ℝ × ℝ => gPart i q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × ℝ => (gPart i q.1).symm q.2) ∧
        (∀ r : ℝ, StrictMono (gPart i r) ∧ StrictMono (gPart i r).symm) ∧
        (∀ r x : ℝ, (gPart i r).symm x = gPart i (-r) x) ∧
        (∀ x : ℝ, gPart i 0 x = x) ∧
        (∀ r : ℝ, tsupport (fun x : ℝ => gPart i r x - x) ⊆ CPart i ∧
          tsupport (fun x : ℝ => (gPart i r).symm x - x) ⊆ CPart i) ∧
        (∀ r x : ℝ, x ∉ CPart i →
          gPart i r x = x ∧ (gPart i r).symm x = x) ∧
        (∀ r x : ℝ, (gPart i r x ∈ V i ↔ x ∈ V i) ∧
          ((gPart i r).symm x ∈ V i ↔ x ∈ V i)) ∧
        (∀ h : ℝ, |h| ≤ width i → ∀ r ∈ Icc (0 : ℝ) 1,
          gPart i r (old i + h) = old i + h + r * (dest i - old i)) ∧
        (∀ h : ℝ, |h| ≤ width i →
          gPart i 1 (old i + h) = dest i + h ∧
          (gPart i 1).symm (dest i + h) = old i + h) ∧
        ContDiff ℝ ∞ (fun q : ℝ × E3 => KPart i q.1 q.2) ∧
        ContDiff ℝ ∞ (fun q : ℝ × E3 => (KPart i q.1).symm q.2) ∧
        (∀ (r : ℝ) (y : E3), KPart i r y =
          L.symm (Phi i (gPart i r (L y).2) ((Phi i (L y).2).symm (L y).1),
            gPart i r (L y).2)) ∧
        (∀ (r : ℝ) (y : E3), (KPart i r).symm y =
          L.symm (Phi i ((gPart i r).symm (L y).2) ((Phi i (L y).2).symm (L y).1),
            (gPart i r).symm (L y).2)) ∧
        (∀ (r : ℝ) (y : E3), H (KPart i r y) = gPart i r (H y) ∧
          H ((KPart i r).symm y) = (gPart i r).symm (H y)) ∧
        (∀ (r : ℝ) (y : E3), (KPart i r y ∈ S ↔ y ∈ S) ∧
          ((KPart i r).symm y ∈ S ↔ y ∈ S)) ∧
        (∀ r : ℝ, KPart i r '' S = S ∧ (KPart i r).symm '' S = S) ∧
        (∀ (r : ℝ) (y : E3), H y ∉ CPart i →
          KPart i r y = y ∧ (KPart i r).symm y = y) ∧
        (∀ r : ℝ, tsupport (fun y : E3 => KPart i r y - y) ⊆ H ⁻¹' CPart i ∧
          tsupport (fun y : E3 => (KPart i r).symm y - y) ⊆ H ⁻¹' CPart i) ∧
        (∀ y : E3, KPart i 0 y = y)) ∧
      Disjoint (V 0) (V 1) ∧
      0 < b ∧ b < tau ∧ b < min (-m) p ∧ b < 1 / 256 ∧
      (∀ i : Fin 2, b < width i) ∧
      0 < etaFix ∧ Icc (-etaFix) etaFix ⊆ (V 0 ∪ V 1)ᶜ ∧
      IsCompact C ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℝ => g q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℝ => (g q.1).symm q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E3 => K q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × E3 => (K q.1).symm q.2) ∧
      (∀ r : ℝ, StrictMono (g r) ∧ StrictMono (g r).symm) ∧
      (∀ x : ℝ, g 0 x = x) ∧ (∀ y : E3, K 0 y = y ∧ (K 0).symm y = y) ∧
      (∀ (r : ℝ) (y : E3), H (K r y) = g r (H y) ∧
        H ((K r).symm y) = (g r).symm (H y)) ∧
      (∀ (r : ℝ) (y : E3), (K r y ∈ S ↔ y ∈ S) ∧
        ((K r).symm y ∈ S ↔ y ∈ S)) ∧
      (∀ r : ℝ, K r '' S = S ∧ (K r).symm '' S = S) ∧
      (∀ r x : ℝ, x ∉ C → g r x = x ∧ (g r).symm x = x) ∧
      (∀ (r : ℝ) (y : E3), H y ∉ C → K r y = y ∧ (K r).symm y = y) ∧
      (∀ r : ℝ, tsupport (fun x : ℝ => g r x - x) ⊆ C ∧
        tsupport (fun x : ℝ => (g r).symm x - x) ⊆ C ∧
        tsupport (fun y : E3 => K r y - y) ⊆ H ⁻¹' C ∧
        tsupport (fun y : E3 => (K r).symm y - y) ⊆ H ⁻¹' C) ∧
      (∀ (r : ℝ) (y : E3), |H y| < etaFix → K r y = y ∧ (K r).symm y = y) ∧
      (∀ (i : Fin 2) (h : ℝ), |h| ≤ width i →
        g 1 (old i + h) = dest i + h ∧ (g 1).symm (dest i + h) = old i + h) ∧
      (∀ r z : ℝ,
        K r '' (S ∩ {y : E3 | H y = z}) = S ∩ {y : E3 | H y = g r z} ∧
        (K r).symm '' (S ∩ {y : E3 | H y = g r z}) = S ∩ {y : E3 | H y = z} ∧
        K r '' (S ∩ {y : E3 | H y ≤ z}) = S ∩ {y : E3 | H y ≤ g r z} ∧
        (K r).symm '' (S ∩ {y : E3 | H y ≤ g r z}) = S ∩ {y : E3 | H y ≤ z} ∧
        K r '' (S ∩ {y : E3 | z ≤ H y}) = S ∩ {y : E3 | g r z ≤ H y} ∧
        (K r).symm '' (S ∩ {y : E3 | g r z ≤ H y}) = S ∩ {y : E3 | z ≤ H y}) ∧
      K 1 '' (S ∩ {y : E3 | (-1 / 8 : ℝ) ≤ H y ∧ H y ≤ 3 / 2}) =
        S ∩ {y : E3 | m ≤ H y ∧ H y ≤ p} ∧
      (K 1).symm '' (S ∩ {y : E3 | m ≤ H y ∧ H y ≤ p}) =
        S ∩ {y : E3 | (-1 / 8 : ℝ) ≤ H y ∧ H y ≤ 3 / 2} ∧
      ∀ r : ℝ,
        K r '' (F '' ball (0 : E3) 1) = F '' ball (0 : E3) 1 ∧
        K r '' (F '' closedBall (0 : E3) 1) = F '' closedBall (0 : E3) 1 ∧
        (K r).symm '' (F '' ball (0 : E3) 1) = F '' ball (0 : E3) 1 ∧
        (K r).symm '' (F '' closedBall (0 : E3) 1) = F '' closedBall (0 : E3) 1 := by
  classical
  let L := heightPlaneCoordinates u
  let F : E3 → E3 := fun y =>
    L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
      (nonnestedReferenceDiffeomorph 0 d hd y).2)
  let j : UnitTwoSphere → E3 := fun q => F (q : E3)
  let psi : UnitTwoSphere × ℝ → E3 := fun q => F ((1 + q.2) • (q.1 : E3))
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S : Set E3 := range j
  let old : Fin 2 → ℝ := ![-1 / 8, 3 / 2]
  let dest : Fin 2 → ℝ := ![m, p]
  let lo : Fin 2 → ℝ := ![-1 / 4, 0]
  let hi : Fin 2 → ℝ := ![0, 2]
  let left : Fin 2 → ℝ := fun i => min (old i) (dest i)
  let right : Fin 2 → ℝ := fun i => max (old i) (dest i)
  let center : Fin 2 → ℝ := fun i => (left i + right i) / 2
  change IsCollarEmbedding psi ∧ _
  let Fd := (nonnestedReferenceDiffeomorph 0 d hd).trans
    ((J2.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toDiffeomorph.trans
      L.symm.toDiffeomorph)
  have hFd (y : E3) : Fd y = F y := rfl
  obtain ⟨rad, _, hradT, _, hradInv, hrad, hradi⟩ :=
    exists_collar_radial_coordinates
      (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞) (side := (1 : ℝ)) (by norm_num)
  let Cchart := rad.symm.trans Fd.toHomeomorph.toOpenPartialHomeomorph
  have hCs : Cchart.source = univ ×ˢ Ioo (-1 : ℝ) 1 := by
    change rad.target ∩ rad.symm ⁻¹' (univ : Set E3) = _
    simpa only [preimage_univ, inter_univ] using hradT
  have hCf : (Cchart : UnitTwoSphere × ℝ → E3) = psi := by
    funext q
    change Fd (rad.symm q) = F ((1 + q.2) • (q.1 : E3))
    rw [hradInv]
    simp only [one_mul, Diffeomorph.coe_refl, id_eq, hFd]
  have hCsm : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
      Cchart Cchart.source :=
    Fd.contMDiff.comp_contMDiffOn (hradi.mono inter_subset_left)
  have hCism : ContMDiffOn 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      Cchart.symm Cchart.target :=
    hrad.comp Fd.symm.contMDiff.contMDiffOn (fun _ hy => hy.2)
  have hCdiff : Cchart.MDifferentiable ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) :=
    ⟨hCsm.mdifferentiableOn (by simp), hCism.mdifferentiableOn (by simp)⟩
  have hpsi : IsCollarEmbedding psi := by
    rw [← hCf]
    refine ⟨by simpa only [hCs] using hCsm, ?_, ?_⟩
    · intro x hx y hy hxy
      exact Cchart.injOn (hCs.symm ▸ hx) (hCs.symm ▸ hy) hxy
    · intro x hx
      exact hCdiff.mfderiv_injective (hCs.symm ▸ hx)
  have hcentral : (fun q : UnitTwoSphere => psi (q, 0)) = j := by
    funext q
    simp only [psi, add_zero, one_smul]
    rfl
  let f : UnitTwoSphere → ℝ := fun q =>
    1 + (q : E3) 2 - ((q : E3) 1) ^ 2 +
      d (((q : E3) 0) ^ 2 + ((q : E3) 1) ^ 2)
  have hNative : (fun q : UnitTwoSphere => ⟪(u : E3), psi (q, 0)⟫_ℝ) = f := by
    funext q
    rw [← heightPlaneCoordinates_snd]
    change (L (F ((1 + (0 : ℝ)) • (q : E3)))).2 = f q
    simp only [add_zero, one_smul, F, L.apply_symm_apply]
    rw [(nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
    simp only [zero_add]
    rfl
  obtain ⟨_, _, _, _, hRegNeg⟩ :=
    exists_nonnested_reference_lower_slices sigma hsigma hsigmaSmall
      d hd hdNear hdZero hdBounds hdDeriv J2 hJ2
  have hd0 : d 0 = 0 := by
    have hh := hdNear 0 (by norm_num) (by linarith)
    simpa using hh
  have hOld (i : Fin 2) : old i ∈ Ioo (lo i) (hi i) := by
    fin_cases i <;> norm_num [old, lo, hi]
  have hDest (i : Fin 2) : dest i ∈ Ioo (lo i) (hi i) := by
    fin_cases i
    · exact hm
    · exact hp
  have hLR (i : Fin 2) : left i ≤ right i :=
    (min_le_left _ _).trans (le_max_left _ _)
  have hInterval (i : Fin 2) : Icc (left i) (right i) ⊆ Ioo (lo i) (hi i) := by
    intro x hx
    exact ⟨(lt_min (hOld i).1 (hDest i).1).trans_le hx.1,
      hx.2.trans_lt (max_lt (hOld i).2 (hDest i).2)⟩
  have hRegular (i : Fin 2) (q : UnitTwoSphere)
      (hq : ⟪(u : E3), psi (q, 0)⟫_ℝ ∈ Icc (left i) (right i)) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun q : UnitTwoSphere => ⟪(u : E3), psi (q, 0)⟫_ℝ) q ≠ 0 := by
    have hqI := hInterval i hq
    change (fun q : UnitTwoSphere => ⟪(u : E3), psi (q, 0)⟫_ℝ) q ∈ _ at hqI
    rw [hNative] at hqI ⊢
    fin_cases i
    · exact hRegNeg q hqI
    · exact nonnested_reference_positive_height_regular d hd hd0
        (fun x hx => (hdBounds x hx).2) hdDeriv q hqI
  have hTransport (i : Fin 2) :=
    exists_regular_collar_horizontal_transport psi hpsi u (left i) (right i)
      (hLR i) (hRegular i)
  choose radius hradius hSpan Phi hPhi hPhii hPhi0 _hPhiSupport hBandRaw using hTransport
  have hBand (i : Fin 2) (z : ℝ)
      (hz : z ∈ Ioo (center i - radius i) (center i + radius i)) (x : E2) :
      L.symm (Phi i z x, z) ∈ S ↔ L.symm (x, center i) ∈ S := by
    simpa only [hcentral] using hBandRaw i z hz x
  have hScalar (i : Fin 2) :=
    reference_scalar_window (lo i) (hi i) (old i) (dest i) (center i) (radius i)
      (hOld i) (hDest i) (hSpan i)
  choose width gPart CPart hwidth hbuffer hC hCV hg hgi hneg hg0 hmono
    hgsupport hgfixed _hgfixedV hgfixedJ hgV htrack haffine using hScalar
  let V : Fin 2 → Set ℝ := fun i =>
    Ioo (left i - 3 * width i) (right i + 3 * width i)
  have hConjugate (i : Fin 2) :=
    reference_cut_conjugacy u S
      (Ioo (center i - radius i) (center i + radius i)) (center i)
      (Phi i) (hPhi i) (hPhii i) (hBand i) (gPart i) (hg i) (hgi i) (hg0 i)
      (fun r x hx => (hgfixedJ i r x hx).1)
  choose KPart hK hKi hKformula hKiformula hHeight hMem hMemInv hImage
    _hKfixedJ hK0 using hConjugate
  change ∀ i r y, H (KPart i r y) = gPart i r (H y) at hHeight
  have hLH (y : E3) : (L y).2 = H y := heightPlaneCoordinates_snd u y
  have hHeightInv (i : Fin 2) (r : ℝ) (y : E3) :
      H ((KPart i r).symm y) = (gPart i r).symm (H y) := by
    have hh := congrArg (gPart i r).symm (hHeight i r ((KPart i r).symm y))
    simpa only [(KPart i r).apply_symm_apply, (gPart i r).symm_apply_apply] using hh.symm
  have hFixed (i : Fin 2) (r : ℝ) (y : E3) (hy : H y ∉ CPart i) :
      KPart i r y = y ∧ (KPart i r).symm y = y := by
    have hf : gPart i r (L y).2 = (L y).2 := by
      simpa only [hLH] using (hgfixed i r (H y) hy).1
    have hi : (gPart i r).symm (L y).2 = (L y).2 := by
      simpa only [hLH] using (hgfixed i r (H y) hy).2
    constructor
    · rw [hKformula]
      change L.symm (Phi i (gPart i r (L y).2) ((Phi i (L y).2).symm (L y).1),
        gPart i r (L y).2) = y
      rw [hf, (Phi i (L y).2).apply_symm_apply, Prod.eta, L.symm_apply_apply]
    · rw [hKiformula]
      change L.symm (Phi i ((gPart i r).symm (L y).2)
        ((Phi i (L y).2).symm (L y).1), (gPart i r).symm (L y).2) = y
      rw [hi, (Phi i (L y).2).apply_symm_apply, Prod.eta, L.symm_apply_apply]
  have hSupport (i : Fin 2) (r : ℝ) :
      tsupport (fun y : E3 => KPart i r y - y) ⊆ H ⁻¹' CPart i ∧
      tsupport (fun y : E3 => (KPart i r).symm y - y) ⊆ H ⁻¹' CPart i := by
    constructor
    · apply closure_minimal ?_ ((hC i).isClosed.preimage H.continuous)
      intro y hy
      change H y ∈ CPart i
      by_contra hn
      exact hy (sub_eq_zero.mpr (hFixed i r y hn).1)
    · apply closure_minimal ?_ ((hC i).isClosed.preimage H.continuous)
      intro y hy
      change H y ∈ CPart i
      by_contra hn
      exact hy (sub_eq_zero.mpr (hFixed i r y hn).2)
  have hEdges (i : Fin 2) :
      lo i < left i - 3 * width i ∧ right i + 3 * width i < hi i := by
    have hleft := (hbuffer i
      (show left i - 4 * width i ∈ Icc (left i - 4 * width i)
        (right i + 4 * width i) from ⟨le_rfl, by linarith [hLR i, hwidth i]⟩)).1.1
    have hright := (hbuffer i
      (show right i + 4 * width i ∈ Icc (left i - 4 * width i)
        (right i + 4 * width i) from ⟨by linarith [hLR i, hwidth i], le_rfl⟩)).1.2
    exact ⟨by linarith [hwidth i], by linarith [hwidth i]⟩
  have hNeg : right 0 + 3 * width 0 < 0 := by simpa [hi] using (hEdges 0).2
  have hPos : 0 < left 1 - 3 * width 1 := by simpa [lo] using (hEdges 1).1
  have hDisjoint : Disjoint (V 0) (V 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' : x < right 0 + 3 * width 0 := hx.2
    have hy' : left 1 - 3 * width 1 < x := hy.1
    linarith
  let etaFix := min (-(right 0 + 3 * width 0)) (left 1 - 3 * width 1) / 2
  have hetaMin : 0 < min (-(right 0 + 3 * width 0)) (left 1 - 3 * width 1) :=
    lt_min (neg_pos.mpr hNeg) hPos
  have heta : 0 < etaFix := div_pos hetaMin (by norm_num)
  have hetaBounds : etaFix < -(right 0 + 3 * width 0) ∧
      etaFix < left 1 - 3 * width 1 := by
    apply lt_min_iff.mp
    dsimp [etaFix]
    linarith
  have hFixedSlab : Icc (-etaFix) etaFix ⊆ (V 0 ∪ V 1)ᶜ := by
    intro x hx hv
    rcases hv with h0 | h1
    · have hh : x < right 0 + 3 * width 0 := h0.2
      linarith [hx.1, hetaBounds.1]
    · have hh : left 1 - 3 * width 1 < x := h1.1
      linarith [hx.2, hetaBounds.2]
  let budget := min tau (min (-m) (min p (min (width 0) (min (width 1) (1 / 512)))))
  have hbudget : 0 < budget :=
    lt_min htau (lt_min (neg_pos.mpr hm.2)
      (lt_min hp.1 (lt_min (hwidth 0) (lt_min (hwidth 1) (by norm_num)))))
  let b := budget / 2
  have hb : 0 < b := div_pos hbudget (by norm_num)
  have hbAll : b < tau ∧ b < -m ∧ b < p ∧ b < width 0 ∧ b < width 1 ∧ b < 1 / 512 := by
    have hh : b < budget := by dsimp [b]; linarith
    simpa only [budget, lt_min_iff] using hh
  have hbWidth (i : Fin 2) : b < width i := by
    fin_cases i
    · exact hbAll.2.2.2.1
    · exact hbAll.2.2.2.2.1
  let g := fun r : ℝ => (gPart 0 r).trans (gPart 1 r)
  let K := fun r : ℝ => (KPart 0 r).trans (KPart 1 r)
  let C : Set ℝ := CPart 0 ∪ CPart 1
  have hCcompact : IsCompact C := (hC 0).union (hC 1)
  have hgsm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => g q.1 q.2) :=
    (hg 1).comp (contDiff_fst.prodMk (hg 0))
  have hgism : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (g q.1).symm q.2) :=
    (hgi 0).comp (contDiff_fst.prodMk (hgi 1))
  have hKsm : ContDiff ℝ ∞ (fun q : ℝ × E3 => K q.1 q.2) :=
    (hK 1).comp (contDiff_fst.prodMk (hK 0))
  have hKism : ContDiff ℝ ∞ (fun q : ℝ × E3 => (K q.1).symm q.2) :=
    (hKi 0).comp (contDiff_fst.prodMk (hKi 1))
  have hMono (r : ℝ) : StrictMono (g r) ∧ StrictMono (g r).symm :=
    ⟨(hmono 1 r).1.comp (hmono 0 r).1, (hmono 0 r).2.comp (hmono 1 r).2⟩
  have hgZero (x : ℝ) : g 0 x = x := by
    change gPart 1 0 (gPart 0 0 x) = x
    rw [hg0, hg0]
  have hKZero (y : E3) : K 0 y = y ∧ (K 0).symm y = y := by
    have hh : K 0 y = y := by
      change KPart 1 0 (KPart 0 0 y) = y
      rw [hK0, hK0]
    refine ⟨hh, ?_⟩
    have hi := congrArg (K 0).symm hh
    simpa only [(K 0).symm_apply_apply] using hi.symm
  have hHeights (r : ℝ) (y : E3) :
      H (K r y) = g r (H y) ∧ H ((K r).symm y) = (g r).symm (H y) := by
    constructor
    · change H (KPart 1 r (KPart 0 r y)) = gPart 1 r (gPart 0 r (H y))
      rw [hHeight, hHeight]
    · change H ((KPart 0 r).symm ((KPart 1 r).symm y)) =
        (gPart 0 r).symm ((gPart 1 r).symm (H y))
      rw [hHeightInv, hHeightInv]
  have hMembership (r : ℝ) (y : E3) :
      (K r y ∈ S ↔ y ∈ S) ∧ ((K r).symm y ∈ S ↔ y ∈ S) :=
    ⟨(hMem 1 r (KPart 0 r y)).trans (hMem 0 r y),
      (hMemInv 0 r ((KPart 1 r).symm y)).trans (hMemInv 1 r y)⟩
  have hImages (r : ℝ) : K r '' S = S ∧ (K r).symm '' S = S := by
    constructor
    · calc
        K r '' S = KPart 1 r '' (KPart 0 r '' S) :=
          (image_image (KPart 1 r) (KPart 0 r) S).symm
        _ = S := by rw [(hImage 0 r).1, (hImage 1 r).1]
    · calc
        (K r).symm '' S = (KPart 0 r).symm '' ((KPart 1 r).symm '' S) :=
          (image_image (KPart 0 r).symm (KPart 1 r).symm S).symm
        _ = S := by rw [(hImage 1 r).2, (hImage 0 r).2]
  have hgFixed (r x : ℝ) (hx : x ∉ C) : g r x = x ∧ (g r).symm x = x := by
    have h0 := hgfixed 0 r x (fun hh => hx (Or.inl hh))
    have h1 := hgfixed 1 r x (fun hh => hx (Or.inr hh))
    change gPart 1 r (gPart 0 r x) = x ∧ (gPart 0 r).symm ((gPart 1 r).symm x) = x
    rw [h0.1, h1.1, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  have hKFixed (r : ℝ) (y : E3) (hy : H y ∉ C) :
      K r y = y ∧ (K r).symm y = y := by
    have h0 := hFixed 0 r y (fun hh => hy (Or.inl hh))
    have h1 := hFixed 1 r y (fun hh => hy (Or.inr hh))
    change KPart 1 r (KPart 0 r y) = y ∧
      (KPart 0 r).symm ((KPart 1 r).symm y) = y
    rw [h0.1, h1.1, h1.2, h0.2]
    exact ⟨rfl, rfl⟩
  have hSupports (r : ℝ) :
      tsupport (fun x : ℝ => g r x - x) ⊆ C ∧
      tsupport (fun x : ℝ => (g r).symm x - x) ⊆ C ∧
      tsupport (fun y : E3 => K r y - y) ⊆ H ⁻¹' C ∧
      tsupport (fun y : E3 => (K r).symm y - y) ⊆ H ⁻¹' C := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply closure_minimal ?_ hCcompact.isClosed
      intro x hx
      by_contra hn
      exact hx (sub_eq_zero.mpr (hgFixed r x hn).1)
    · apply closure_minimal ?_ hCcompact.isClosed
      intro x hx
      by_contra hn
      exact hx (sub_eq_zero.mpr (hgFixed r x hn).2)
    · apply closure_minimal ?_ (hCcompact.isClosed.preimage H.continuous)
      intro y hy
      change H y ∈ C
      by_contra hn
      exact hy (sub_eq_zero.mpr (hKFixed r y hn).1)
    · apply closure_minimal ?_ (hCcompact.isClosed.preimage H.continuous)
      intro y hy
      change H y ∈ C
      by_contra hn
      exact hy (sub_eq_zero.mpr (hKFixed r y hn).2)
  have hSlab (r : ℝ) (y : E3) (hy : |H y| < etaFix) :
      K r y = y ∧ (K r).symm y = y := by
    apply hKFixed r y
    intro hyC
    have hnot := hFixedSlab (abs_le.mp hy.le)
    exact hnot (hyC.elim (fun hh => Or.inl (hCV 0 hh)) (fun hh => Or.inr (hCV 1 hh)))
  have hOffset (i : Fin 2) (h : ℝ) (hh : |h| ≤ width i) :
      old i + h ∈ V i ∧ dest i + h ∈ V i := by
    have hh' := abs_le.mp hh
    have h0 : left i ≤ old i := min_le_left _ _
    have h1 : left i ≤ dest i := min_le_right _ _
    have h2 : old i ≤ right i := le_max_left _ _
    have h3 : dest i ≤ right i := le_max_right _ _
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [hwidth i]
  have hCross01 (r x : ℝ) (hx : x ∈ V 0) :
      gPart 1 r x = x ∧ (gPart 1 r).symm x = x :=
    hgfixed 1 r x (fun hy => Set.disjoint_left.mp hDisjoint hx (hCV 1 hy))
  have hCross10 (r x : ℝ) (hx : x ∈ V 1) :
      gPart 0 r x = x ∧ (gPart 0 r).symm x = x :=
    hgfixed 0 r x (fun hy => Set.disjoint_left.mp hDisjoint (hCV 0 hy) hx)
  have hAffine (i : Fin 2) (h : ℝ) (hh : |h| ≤ width i) :
      g 1 (old i + h) = dest i + h ∧ (g 1).symm (dest i + h) = old i + h := by
    fin_cases i
    · have ha := haffine 0 h hh
      have hc := hCross01 1 (dest 0 + h) (hOffset 0 h hh).2
      change gPart 1 1 (gPart 0 1 (old 0 + h)) = dest 0 + h ∧
        (gPart 0 1).symm ((gPart 1 1).symm (dest 0 + h)) = old 0 + h
      rw [ha.1, hc.1, hc.2, ha.2]
      exact ⟨rfl, rfl⟩
    · have ha := haffine 1 h hh
      have hc := hCross10 1 (old 1 + h) (hOffset 1 h hh).1
      change gPart 1 1 (gPart 0 1 (old 1 + h)) = dest 1 + h ∧
        (gPart 0 1).symm ((gPart 1 1).symm (dest 1 + h)) = old 1 + h
      rw [hc.1, ha.1, ha.2, hc.2]
      exact ⟨rfl, rfl⟩
  have hPredicateImage (r : ℝ) (P Q : ℝ → Prop) (hPQ : ∀ x : ℝ, P (g r x) ↔ Q x) :
      K r '' (S ∩ {y : E3 | Q (H y)}) = S ∩ {y : E3 | P (H y)} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hqx⟩, rfl⟩
      refine ⟨(hMembership r x).1.mpr hx, ?_⟩
      change P (H (K r x))
      rw [(hHeights r x).1]
      exact (hPQ (H x)).mpr hqx
    · rintro ⟨hy, hpy⟩
      refine ⟨(K r).symm y, ⟨(hMembership r y).2.mpr hy, ?_⟩, (K r).apply_symm_apply y⟩
      apply (hPQ (H ((K r).symm y))).mp
      rwa [← (hHeights r ((K r).symm y)).1, (K r).apply_symm_apply]
  have hLevels (r z : ℝ) :
      K r '' (S ∩ {y : E3 | H y = z}) = S ∩ {y : E3 | H y = g r z} ∧
      (K r).symm '' (S ∩ {y : E3 | H y = g r z}) = S ∩ {y : E3 | H y = z} ∧
      K r '' (S ∩ {y : E3 | H y ≤ z}) = S ∩ {y : E3 | H y ≤ g r z} ∧
      (K r).symm '' (S ∩ {y : E3 | H y ≤ g r z}) = S ∩ {y : E3 | H y ≤ z} ∧
      K r '' (S ∩ {y : E3 | z ≤ H y}) = S ∩ {y : E3 | g r z ≤ H y} ∧
      (K r).symm '' (S ∩ {y : E3 | g r z ≤ H y}) = S ∩ {y : E3 | z ≤ H y} := by
    have hlevel := hPredicateImage r (fun x => x = g r z) (fun x => x = z)
      (fun _ => (g r).injective.eq_iff)
    have hlower := hPredicateImage r (fun x => x ≤ g r z) (fun x => x ≤ z)
      (fun _ => (hMono r).1.le_iff_le)
    have hupper := hPredicateImage r (fun x => g r z ≤ x) (fun x => z ≤ x)
      (fun _ => (hMono r).1.le_iff_le)
    refine ⟨hlevel, ?_, hlower, ?_, hupper, ?_⟩
    · rw [← hlevel]
      exact (K r).symm_image_image _
    · rw [← hlower]
      exact (K r).symm_image_image _
    · rw [← hupper]
      exact (K r).symm_image_image _
  have hOldImage : g 1 (-1 / 8) = m ∧ g 1 (3 / 2) = p := by
    constructor
    · simpa [old, dest] using (hAffine 0 0 (by simpa using (hwidth 0).le)).1
    · simpa [old, dest] using (hAffine 1 0 (by simpa using (hwidth 1).le)).1
  have hMiddle : K 1 '' (S ∩ {y : E3 | (-1 / 8 : ℝ) ≤ H y ∧ H y ≤ 3 / 2}) =
      S ∩ {y : E3 | m ≤ H y ∧ H y ≤ p} := by
    apply hPredicateImage 1 (fun x => m ≤ x ∧ x ≤ p)
      (fun x => (-1 / 8 : ℝ) ≤ x ∧ x ≤ 3 / 2)
    intro x
    rw [← hOldImage.1, ← hOldImage.2]
    exact and_congr (hMono 1).1.le_iff_le (hMono 1).1.le_iff_le
  have hMiddleInv : (K 1).symm '' (S ∩ {y : E3 | m ≤ H y ∧ H y ≤ p}) =
      S ∩ {y : E3 | (-1 / 8 : ℝ) ≤ H y ∧ H y ≤ 3 / 2} := by
    rw [← hMiddle]
    exact (K 1).symm_image_image _
  let B0 : BallNeighborhoodChart E3 E3 := {
    chart := Fd.toHomeomorph.toOpenPartialHomeomorph
    closedBall_subset_source := subset_univ _
    smooth := Fd.contDiff.contDiffOn
    smooth_symm := Fd.symm.contDiff.contDiffOn }
  have hB0 : B0.boundary = S := by
    change F '' sphere (0 : E3) 1 = range j
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟨x, hx⟩ : UnitTwoSphere), rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q : E3), q.property, rfl⟩
  have hdim : 1 < Module.rank ℝ E3 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E3]
  have hRegion (Y : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (hY : Y '' S = S) :
      Y '' (F '' ball (0 : E3) 1) = F '' ball (0 : E3) 1 ∧
      Y '' (F '' closedBall (0 : E3) 1) = F '' closedBall (0 : E3) 1 := by
    have hbd : (B0.mapDiffeomorph Y).boundary = B0.boundary := by
      rw [B0.mapDiffeomorph_boundary, hB0, hY]
    have hi := (B0.mapDiffeomorph Y).inside_eq_of_boundary_eq B0 hdim hbd
    have hc := (B0.mapDiffeomorph Y).closedRegion_eq_of_boundary_eq B0 hdim hbd
    rw [B0.mapDiffeomorph_inside] at hi
    rw [B0.mapDiffeomorph_closedRegion] at hc
    exact ⟨hi, hc⟩
  refine ⟨hpsi, radius, width, Phi, gPart, KPart, CPart, b, etaFix, ?_,
    hDisjoint, hb, hbAll.1, lt_min hbAll.2.1 hbAll.2.2.1,
    by linarith [hbAll.2.2.2.2.2], hbWidth, heta, hFixedSlab, hCcompact,
    hgsm, hgism, hKsm, hKism, hMono, hgZero, hKZero, hHeights, hMembership, hImages,
    hgFixed, hKFixed, hSupports, hSlab, hAffine, hLevels, hMiddle, hMiddleInv, ?_⟩
  · intro i
    exact ⟨hradius i, hwidth i, hSpan i, hbuffer i, hPhi i, hPhii i, hPhi0 i,
      hBand i, hC i, hCV i, hg i, hgi i, hmono i, hneg i, hg0 i, hgsupport i,
      hgfixed i, hgV i, htrack i, haffine i, hK i, hKi i, hKformula i, hKiformula i,
      fun r y => ⟨hHeight i r y, hHeightInv i r y⟩,
      fun r y => ⟨hMem i r y, hMemInv i r y⟩, hImage i, hFixed i, hSupport i, hK0 i⟩
  · intro r
    exact ⟨(hRegion (K r) (hImages r).1).1, (hRegion (K r) (hImages r).1).2,
      (hRegion (K r).symm (hImages r).2).1, (hRegion (K r).symm (hImages r).2).2⟩

end PoincareConjecture.M25.Topology3D
