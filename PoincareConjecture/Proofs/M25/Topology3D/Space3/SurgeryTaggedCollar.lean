import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryWeightedCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNewCapTag
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_retained_collar_chart
    (psi psiNew : UnitTwoSphere × ℝ → E3)
    (N : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere)
    (hN : ContMDiffOn (𝓡 2) (𝓡 2) ∞ N N.source)
    (hNi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ N.symm N.target)
    (K : Set UnitTwoSphere) (hK : K ⊆ N.source) (gamma : ℝ)
    (hgerm : ∀ᶠ p in 𝓝ˢ K, ∀ s : ℝ, |s| < 1 →
      psiNew (p, s) = psi (N p, gamma * s)) :
    ∃ e : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere,
      e.source ⊆ N.source ∧ e.target ⊆ N.target ∧
      (∀ p, e p = N p) ∧ (∀ p, e.symm p = N.symm p) ∧
      K ⊆ e.source ∧ N '' K ⊆ e.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ p ∈ e.source, ∀ s : ℝ, |s| < 1 →
        psiNew (p, s) = psi (e p, gamma * s) := by
  obtain ⟨U, hU, hKU, hUP⟩ := mem_nhdsSet_iff_exists.mp hgerm
  let e := N.restrOpen U hU
  have hs : e.source ⊆ N.source := fun _ hp => hp.1
  have ht : e.target ⊆ N.target := fun _ hp => hp.1
  have hKe : K ⊆ e.source := fun _ hp => ⟨hK hp, hKU hp⟩
  refine ⟨e, hs, ht, fun _ => rfl, fun _ => rfl, hKe, ?_,
    hN.mono hs, hNi.mono ht, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact e.map_source (hKe hp)
  · intro p hp s hstime
    exact hUP hp.2 s hstime

theorem exists_surgery_replacement_tagged_collar
    (P : SurgeryCapProfile) (psi : UnitTwoSphere × ℝ → E3)
    (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData psi u t)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (hem : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hRball : R '' closedBall 0 1 = closedBall 0 r)
    (hR : ∀ x ∈ sphere (0 : E2) 1, R x = r • x)
    (hRnear : ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
      R x = surgeryMatchingRadius r (l / k) ‖x‖ • NormedSpace.normalize x)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ e.source ∧
      e x = D.sourceCollar (circleDirection x, sigma * (k * (1 - ‖x‖))))
    (hl : 0 < l) (hlM : l * P.heightBound < k * (1 - r) / 4)
    {W : Set E3} (hW : IsOpen W)
    (hjW : range (P.replacementMap psi R e D.tube t sigma r k l) ⊆ W)
    {b : ℝ} (hb : 0 < b) :
    ∃ psiNew : UnitTwoSphere × ℝ → E3,
      ∃ ret : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere,
      ∃ gamma : ℝ, ∃ C : SurgeryCapTag psiNew u,
        IsCollarEmbedding psiNew ∧
        (∀ p, psiNew (p, 0) = P.replacementMap psi R e D.tube t sigma r k l p) ∧
        MapsTo psiNew (univ ×ˢ Ioo (-1) 1) W ∧
        gamma ≠ 0 ∧ |gamma| < min b 1 ∧ |C.beta| < min b 1 ∧
        ret.source ⊆ (surgeryNorthChart R e).source ∧
        ret.target ⊆ (surgeryNorthChart R e).target ∧
        (∀ p, ret p = surgeryNorthChart R e p) ∧
        (∀ p, ret.symm p = (surgeryNorthChart R e).symm p) ∧
        {p : UnitTwoSphere | 0 ≤ (heightCoordinates (p : E3)).2} ⊆ ret.source ∧
        e '' closedBall 0 r ⊆ ret.target ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ ret ret.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ ret.symm ret.target ∧
        (∀ p ∈ ret.source, ∀ s : ℝ, |s| < 1 →
          psiNew (p, s) = psi (ret p, gamma * s)) ∧
        C.profile = P ∧ C.tube = D.tube ∧ C.cutHeight = t ∧
        C.removal = k * (1 - r) ∧ C.scale = l ∧ C.sign = sigma ∧
        C.sourceChart = OpenPartialHomeomorph.refl UnitTwoSphere ∧
        C.flatChart = southSphereChart ∧ C.collarWidth = 1 ∧
        C.sourceCap = {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
        C.cap = P.capMap D.tube t sigma (k * (1 - r)) l ''
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
        C.seam = P.capMap D.tube t sigma (k * (1 - r)) l ''
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} := by
  obtain ⟨_beta0, N, eps, w, tau, _, _, htau, hsmall, _, _, _, heps,
    _, _, _, _, _, _, hcollar⟩ := exists_surgery_replacement_weighted_collar
      P psi hpsi u t D R e he hem hei sigma hsigma hr hr1 hrdelta hk hcwidth
      hRball hR hRnear hnear hl hlM hW hjW hb
  let psiNew := fun z : UnitTwoSphere × ℝ =>
    weightedSphereTimeMap (P.replacementMap psi R e D.tube t sigma r k l) N
      ![fun z => psi (surgeryNorthChart R e z.1, z.2),
        fun z => D.tube ((heightCoordinates (z.1 : E3)).1,
          t + sigma * (k * (1 - r) - l) + z.2)] eps w (z.1, tau * z.2)
  obtain ⟨hpsiNew, hcenter, hmaps, hpatch, _⟩ := hcollar tau htau le_rfl
  change (∀ p, psiNew (p, 0) =
    P.replacementMap psi R e D.tube t sigma r k l p) at hcenter
  have habs (i : Fin 2) : |eps i * tau| = tau := by
    rw [abs_mul, heps, abs_of_pos htau, one_mul]
  have hne (i : Fin 2) : eps i * tau ≠ 0 :=
    abs_pos.mp (by rw [habs]; exact htau)
  have hold : ∀ᶠ p in 𝓝ˢ {p : UnitTwoSphere | 0 ≤ (heightCoordinates (p : E3)).2},
      ∀ s : ℝ, |s| < 1 →
        psiNew (p, s) = psi (surgeryNorthChart R e p, (eps 0 * tau) * s) := hpatch 0
  obtain ⟨ret, hsrc, htar, hret, hretinv, hretK, himage, hsm, hsi, heq⟩ :=
    exists_retained_collar_chart psi psiNew (surgeryNorthChart R e)
      (surgeryNorthChart_contMDiffOn R e hem)
      (surgeryNorthChart_symm_contMDiffOn R e hei)
      {p : UnitTwoSphere | 0 ≤ (heightCoordinates (p : E3)).2}
      (surgeryNorthChart_contains_hemisphere R e he hr1.le hRball) (eps 0 * tau) hold
  have htarget : e '' closedBall 0 r ⊆ ret.target := by
    rw [← surgeryNorthChart_image_hemisphere R e hRball]
    exact himage
  obtain ⟨d, hd, hoverlap⟩ := exists_surgery_replacement_overlap
    P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    P.horizontal_near P.vertical_far psi u t D R e sigma hsigma
    hr hr1 hrdelta hk hcwidth hRnear hnear
  let eta := min d (1 / 4)
  have heta : 0 < eta := lt_min hd (by norm_num)
  have hcentral : ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < eta →
      psiNew (q, 0) = P.capMap D.tube t sigma (k * (1 - r)) l q := by
    intro q hq
    rw [hcenter]
    exact levelPaste_eqOn_lower (fun p : UnitTwoSphere => (heightCoordinates (p : E3)).2)
      (fun p => psi (surgeryNorthChart R e p, 0))
      (P.capMap D.tube t sigma (k * (1 - r)) l) hd
      (fun p hp => (hoverlap p hp).2) (hq.trans_le (min_le_left _ _))
  have hflat : ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 0 →
      ‖(heightCoordinates (q : E3)).1‖ ≤ 1 / 8 → ∀ s : ℝ, |s| < 1 →
        psiNew (q, s) = D.tube ((heightCoordinates (q : E3)).1,
          t + sigma * (k * (1 - r) - l) + (eps 1 * tau) * s) := by
    intro q hq hx s hs
    exact (hpatch 1).self_of_nhdsSet q ⟨hq, hx⟩ s hs
  let C := SurgeryCapTag.of_cap_patch P psiNew u D.tube D.tube_source
    D.tube_smooth D.tube_inverse (fun p _ => D.tube_height p)
    t (k * (1 - r)) l sigma (mul_pos hk (sub_pos.mpr hr1)) hl hsigma hlM
    eta heta (min_le_right _ _) hcentral (eps 1 * tau) (hne 1)
    1 zero_lt_one le_rfl hflat
  refine ⟨psiNew, ret, eps 0 * tau, C, hpsiNew, hcenter, hmaps, hne 0,
    ?_, ?_, hsrc, htar, hret, hretinv, hretK, htarget, hsm, hsi, heq,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rwa [habs]
  · change |eps 1 * tau| < min b 1
    rwa [habs]
  · change (fun q : UnitTwoSphere => q) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} = _
    exact image_id _
  · rw [C.cap_eq_image]
    rfl
  · rw [C.seam_eq_image]
    rfl

end PoincareConjecture.M25.Topology3D
