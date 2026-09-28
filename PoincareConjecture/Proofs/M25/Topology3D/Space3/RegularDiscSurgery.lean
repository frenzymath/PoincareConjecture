import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryTaggedCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryPair












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D




theorem exists_regular_disc_surgery (P : SurgeryCapProfile)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData psi u t) :
    ∃ delta r l : ℝ, ∃ R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
      ∃ child : Fin 2 → UnitTwoSphere × ℝ → E3,
      let e : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere :=
        ![D.sourceDiscs.positive, D.sourceDiscs.negative]
      let sigma : Fin 2 → ℝ := ![1, -1]
      0 < delta ∧ 0 < r ∧ r < 1 ∧ 1 - r < delta ∧
      0 < D.width / 2 * (1 - r) ∧ D.width / 2 * (1 - r) < D.width ∧
      0 < l ∧ l * P.heightBound < D.width / 2 * (1 - r) / 4 ∧
      R '' ball 0 1 = ball 0 r ∧ R '' closedBall 0 1 = closedBall 0 r ∧
      (∀ x ∈ sphere (0 : E2) 1, R x = r • x) ∧
      (∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
        R x = surgeryMatchingRadius r (l / (D.width / 2)) ‖x‖ •
          NormedSpace.normalize x) ∧
      (∀ i (x : E2), |‖x‖ - 1| < delta → x ∈ (e i).source ∧
        e i x = D.sourceCollar (circleDirection x,
          sigma i * (D.width / 2 * (1 - ‖x‖)))) ∧
      (∀ i, IsCollarEmbedding (child i) ∧
        (∀ p, child i (p, 0) =
          P.replacementMap psi R (e i) D.tube t (sigma i) r (D.width / 2) l p) ∧
        child i '' (univ ×ˢ ({0} : Set ℝ)) =
          (fun p : UnitTwoSphere => psi (p, 0)) '' (e i '' closedBall 0 r) ∪
          P.capMap D.tube t (sigma i) (D.width / 2 * (1 - r)) l ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
        ∃ ret : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere,
          ∃ gamma : ℝ, ∃ C : SurgeryCapTag (child i) u,
            gamma ≠ 0 ∧ |gamma| < 1 ∧ |C.beta| < 1 ∧
            ret.source ⊆ (surgeryNorthChart R (e i)).source ∧
            ret.target ⊆ (surgeryNorthChart R (e i)).target ∧
            (∀ p, ret p = surgeryNorthChart R (e i) p) ∧
            (∀ p, ret.symm p = (surgeryNorthChart R (e i)).symm p) ∧
            {p : UnitTwoSphere | 0 ≤ (heightCoordinates (p : E3)).2} ⊆ ret.source ∧
            e i '' closedBall 0 r ⊆ ret.target ∧
            ContMDiffOn (𝓡 2) (𝓡 2) ∞ ret ret.source ∧
            ContMDiffOn (𝓡 2) (𝓡 2) ∞ ret.symm ret.target ∧
            (∀ p ∈ ret.source, ∀ s : ℝ, |s| < 1 →
              child i (p, s) = psi (ret p, gamma * s)) ∧
            C.profile = P ∧ C.tube = D.tube ∧ C.cutHeight = t ∧
            C.removal = D.width / 2 * (1 - r) ∧ C.scale = l ∧ C.sign = sigma i ∧
            C.sourceChart = OpenPartialHomeomorph.refl UnitTwoSphere ∧
            C.flatChart = southSphereChart ∧ C.collarWidth = 1 ∧
            C.sourceCap = {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
            C.cap = P.capMap D.tube t (sigma i) (D.width / 2 * (1 - r)) l ''
              {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
            C.seam = P.capMap D.tube t (sigma i) (D.width / 2 * (1 - r)) l ''
              {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0}) ∧
      Disjoint (child 0 '' (univ ×ˢ ({0} : Set ℝ)))
        (child 1 '' (univ ×ˢ ({0} : Set ℝ))) := by
  classical
  obtain ⟨delta, r, l, R, hd, hr, hr1, hrd, hc, hcw, hl, hlM,
    hRo, hRc, hRs, hRn, hpos, hneg, _, _, _, _, hdisjoint⟩ :=
    exists_smooth_surgery_pair P psi hpsi u t D
  let e : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere :=
    ![D.sourceDiscs.positive, D.sourceDiscs.negative]
  let sigma : Fin 2 → ℝ := ![1, -1]
  have hk : 0 < D.width / 2 := by linarith [D.width_pos]
  have he (i : Fin 2) : closedBall 0 1 ⊆ (e i).source := by
    fin_cases i
    · exact D.sourceDiscs.positive_source
    · exact D.sourceDiscs.negative_source
  have hem (i : Fin 2) : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ (e i) (e i).source := by
    fin_cases i
    · exact D.sourceDiscs.positive_smooth
    · exact D.sourceDiscs.negative_smooth
  have hei (i : Fin 2) : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ (e i).symm (e i).target := by
    fin_cases i
    · exact D.sourceDiscs.positive_inverse
    · exact D.sourceDiscs.negative_inverse
  have hsigma (i : Fin 2) : |sigma i| = 1 := by
    fin_cases i <;> norm_num [sigma]
  have hnear (i : Fin 2) : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ (e i).source ∧
      e i x = D.sourceCollar (circleDirection x,
        sigma i * (D.width / 2 * (1 - ‖x‖))) := by
    fin_cases i
    · simpa [e, sigma] using hpos
    · simpa [e, sigma] using hneg
  choose child ret gamma C hchild hcenter _hmaps hgamma hgammaSmall hbetaSmall
    hsrc htar hret hreti hretK htarget hsm hsi heq hprofile htube hcut
    hremoval hscale hsign hidentity hflat hwidth hsourceCap hcap hseam using
      fun i : Fin 2 => exists_surgery_replacement_tagged_collar
        P psi hpsi u t D R (e i) (he i) (hem i) (hei i) (sigma i) (hsigma i)
        hr hr1 hrd hk hcw hRc hRs hRn (hnear i) hl hlM
        isOpen_univ (subset_univ _) zero_lt_one
  have hcentralImage (i : Fin 2) : child i '' (univ ×ˢ ({0} : Set ℝ)) =
      range (P.replacementMap psi R (e i) D.tube t (sigma i) r (D.width / 2) l) := by
    ext y
    constructor
    · rintro ⟨⟨p, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      rw [hcenter]
      exact mem_range_self p
    · rintro ⟨p, rfl⟩
      exact ⟨(p, 0), ⟨mem_univ _, rfl⟩, hcenter i p⟩
  refine ⟨delta, r, l, R, child, hd, hr, hr1, hrd, hc, hcw, hl, hlM,
    hRo, hRc, hRs, hRn, hnear, ?_, ?_⟩
  · intro i
    refine ⟨hchild i, hcenter i, ?_, ret i, gamma i, C i, hgamma i,
      ?_, ?_, hsrc i, htar i, hret i, hreti i, hretK i, htarget i,
      hsm i, hsi i, heq i, hprofile i, htube i, hcut i, hremoval i,
      hscale i, hsign i, hidentity i, hflat i, hwidth i, hsourceCap i,
      hcap i, hseam i⟩
    · rw [hcentralImage]
      exact P.replacementMap_range psi u t D R (e i) (sigma i) (hsigma i)
        hr hr1 hrd hk hcw hRc hRs (hnear i)
    · simpa only [min_self] using hgammaSmall i
    · simpa only [min_self] using hbetaSmall i
  · rw [hcentralImage 0, hcentralImage 1]
    exact hdisjoint

end PoincareConjecture.M25.Topology3D
