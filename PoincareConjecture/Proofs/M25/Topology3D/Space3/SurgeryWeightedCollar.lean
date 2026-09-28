import PoincareConjecture.Proofs.M25.Topology3D.Space3.WeightedSphereCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereCandidateSign
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCollarCandidates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCollarPatches
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryPairImage
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgerySmoothReplacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ImmersedSphereNormal













set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Manifold InnerProductSpace Topology BigOperators

namespace PoincareConjecture.M25.Topology3D




theorem exists_surgery_north_collar_band
    (P : SurgeryCapProfile) (psi : UnitTwoSphere × ℝ → E3)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData psi u t)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hRball : R '' closedBall 0 1 = closedBall 0 r)
    (hRnear : ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
      R x = surgeryMatchingRadius r (l / k) ‖x‖ • NormedSpace.normalize x)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta → x ∈ e.source ∧
      e x = D.sourceCollar (circleDirection x, sigma * (k * (1 - ‖x‖)))) :
    ∃ beta > (0 : ℝ), beta ≤ 1 / 4 ∧
      ∀ p : UnitTwoSphere, -beta < (heightCoordinates (p : E3)).2 →
        p ∈ (surgeryNorthChart R e).source ∧
        P.replacementMap psi R e D.tube t sigma r k l p =
          psi (surgeryNorthChart R e p, 0) := by
  let H := fun p : UnitTwoSphere => (heightCoordinates (p : E3)).2
  let f := fun p : UnitTwoSphere => psi (surgeryNorthChart R e p, 0)
  let g := P.capMap D.tube t sigma (k * (1 - r)) l
  obtain ⟨d, hd, hoverlap⟩ := exists_surgery_replacement_overlap
    P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    P.horizontal_near P.vertical_far psi u t D R e sigma hsigma
    hr hr1 hrdelta hk hcwidth hRnear hnear
  refine ⟨min d (1 / 4), lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro p hp
  have hpband : -d < H p := by
    change -min d (1 / 4) < H p at hp
    linarith [min_le_left d (1 / 4)]
  have hpeq : P.replacementMap psi R e D.tube t sigma r k l p = f p :=
    levelPaste_eqOn_upper H f g hd (fun q hq => (hoverlap q hq).2) hpband
  refine ⟨?_, hpeq⟩
  by_cases hpn : 0 ≤ H p
  · exact surgeryNorthChart_contains_hemisphere R e he hr1.le hRball hpn
  · exact (hoverlap p (abs_lt.mpr ⟨hpband, (lt_of_not_ge hpn).trans hd⟩)).1





theorem exists_surgery_replacement_weighted_collar
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
    let j := P.replacementMap psi R e D.tube t sigma r k l
    let A : Fin 2 → UnitTwoSphere × ℝ → E3 :=
      ![fun z => psi (surgeryNorthChart R e z.1, z.2),
        fun z => D.tube ((heightCoordinates (z.1 : E3)).1,
          t + sigma * (k * (1 - r) - l) + z.2)]
    let K : Fin 2 → Set UnitTwoSphere :=
      ![{p | 0 ≤ (heightCoordinates (p : E3)).2},
        {p | (heightCoordinates (p : E3)).2 ≤ 0 ∧
          ‖(heightCoordinates (p : E3)).1‖ ≤ 1 / 8}]
    ∃ beta : ℝ, ∃ N : UnitTwoSphere → E3, ∃ eps : Fin 2 → ℝ,
      ∃ w : Fin 2 → UnitTwoSphere → ℝ, ∃ tau0 : ℝ,
      let V : Fin 2 → Set UnitTwoSphere :=
        ![{p | -beta < (heightCoordinates (p : E3)).2},
          {p | (heightCoordinates (p : E3)).2 < -31 / 32}]
      0 < beta ∧ beta ≤ 1 / 4 ∧ 0 < tau0 ∧ tau0 < min b 1 ∧
      ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N ∧ (∀ p, ‖N p‖ = 1) ∧
      (∀ p (v : TangentSpace (𝓡 2) p),
        ⟪N p, mfderiv (𝓡 2) 𝓘(ℝ, E3) j p v⟫_ℝ = 0) ∧
      (∀ i, |eps i| = 1) ∧
      (∀ i, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (w i)) ∧
      (∀ i, tsupport (w i) ⊆ V i) ∧
      (∀ i p, w i p ∈ Icc 0 1) ∧
      (∀ p, (∑ i : Fin 2, w i p) ≤ 1) ∧
      (∀ i, ∀ᶠ p in 𝓝ˢ (K i), w i p = 1) ∧
      (∀ i p, p ∈ V i →
        0 < ⟪N p, eps i • deriv (fun s : ℝ => A i (p, s)) 0⟫_ℝ) ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
        let psiNew := fun z : UnitTwoSphere × ℝ =>
          weightedSphereTimeMap j N A eps w (z.1, tau * z.2)
        IsCollarEmbedding psiNew ∧ (∀ p, psiNew (p, 0) = j p) ∧
        MapsTo psiNew (univ ×ˢ Ioo (-1) 1) W ∧
        (∀ i, ∀ᶠ p in 𝓝ˢ (K i), ∀ s : ℝ, |s| < 1 →
          psiNew (p, s) = A i (p, eps i * tau * s)) ∧
        ∀ i p s, w i p ≠ 0 → |s| < 1 →
          p ∈ V i ∧ eps i * tau * s ∈ Ioo (-1 : ℝ) 1 := by
  classical
  let j := P.replacementMap psi R e D.tube t sigma r k l
  let H := fun p : UnitTwoSphere => (heightCoordinates (p : E3)).2
  let X := fun p : UnitTwoSphere => (heightCoordinates (p : E3)).1
  let A : Fin 2 → UnitTwoSphere × ℝ → E3 :=
    ![fun z => psi (surgeryNorthChart R e z.1, z.2),
      fun z => D.tube (X z.1, t + sigma * (k * (1 - r) - l) + z.2)]
  let K : Fin 2 → Set UnitTwoSphere :=
    ![{p | 0 ≤ H p}, {p | H p ≤ 0 ∧ ‖X p‖ ≤ 1 / 8}]
  obtain ⟨hj, himm, hclosed⟩ := surgeryReplacementMap_smooth_closedEmbedding
    P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    P.horizontal_pos P.horizontal_bound P.vertical_pos P.horizontal_near P.vertical_far
    psi hpsi u t D R e he hem hei sigma hsigma hr hr1 hrdelta hk hcwidth
    hRball hR hRnear hnear hl hlM P.height_bound
  have hinj : Function.Injective j := hclosed.injective
  obtain ⟨N, hN, hunit, horth⟩ := exists_immersed_sphere_unit_normal j hj himm
  obtain ⟨beta, hbeta, hbeta1, hband⟩ := exists_surgery_north_collar_band
    P psi u t D R e he sigma hsigma hr hr1 hrdelta hk hcwidth hRball hRnear hnear
  let V : Fin 2 → Set UnitTwoSphere := ![{p | -beta < H p}, {p | H p < -31 / 32}]
  obtain ⟨hV, hconnected, hK, hKV, hdis, hflat⟩ := surgery_collar_patch_geometry hbeta hbeta1
  obtain ⟨hAold, hAoldfull⟩ := north_collar_candidate_regular psi hpsi
    (surgeryNorthChart R e) (surgeryNorthChart_contMDiffOn R e hem)
    (surgeryNorthChart_symm_contMDiffOn R e hei)
  obtain ⟨hAcap, hAcapfull⟩ := flat_tube_candidate_regular D.tube D.tube_source
    D.tube_smooth D.tube_inverse (t + sigma * (k * (1 - r) - l))
  have hA (i : Fin 2) : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ (A i)
      (V i ×ˢ Ioo (-1) 1) := by
    fin_cases i
    · exact hAold.mono (fun z hz => ⟨(hband z.1 hz.1).1, hz.2⟩)
    · exact hAcap.contMDiffOn
  have hAcentral (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ V i) : A i (p, 0) = j p := by
    fin_cases i
    · exact (hband p hp).2.symm
    · have hpflat := hflat p hp
      have hcoord := surgeryCapCoordinates_flat_south
        P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
        P.horizontal_far P.vertical_near t sigma (k * (1 - r)) l p
        hpflat.2.le hpflat.1.le
      change D.tube (X p, t + sigma * (k * (1 - r) - l) + 0) =
        levelPaste H (fun q => psi (surgeryNorthChart R e q, 0))
          (P.capMap D.tube t sigma (k * (1 - r)) l) p
      rw [levelPaste_of_neg H _ _ hpflat.1]
      change D.tube (X p, t + sigma * (k * (1 - r) - l) + 0) =
        D.tube (surgeryCapCoordinates P.horizontal P.vertical
          P.horizontal_smooth P.vertical_smooth
          (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
          t sigma (k * (1 - r)) l p)
      rw [hcoord, add_zero]
  have hAfull (i : Fin 2) (p : UnitTwoSphere) (hp : p ∈ V i) :
      Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) (A i) (p, 0)) := by
    fin_cases i
    · exact hAoldfull p (hband p hp).1
    · exact hAcapfull p (hflat p hp).1
  have hsign (i : Fin 2) : ∃ eps : ℝ, |eps| = 1 ∧ ∀ p ∈ V i,
      0 < ⟪N p, eps • deriv (fun s : ℝ => A i (p, s)) 0⟫_ℝ :=
    exists_sphere_candidate_time_sign j N (A i) (hV i) (hconnected i)
      zero_lt_one hj hN hunit horth (hA i) (hAcentral i) (hAfull i)
  choose eps heps hpos using hsign
  obtain ⟨w, hw, hsupport, hwnear, hrange, _, hsum⟩ :=
    exists_two_sphere_cutoffs K V hK hV hKV hdis
  obtain ⟨tau0, htau0, hsmall, hcollar⟩ := exists_weighted_sphere_collar
    j N A eps w V zero_lt_one hj hN hinj himm hunit horth hV hA hAcentral
    heps hpos hw hsupport hrange hsum hW hjW hb
  refine ⟨beta, N, eps, w, tau0, hbeta, hbeta1, htau0, hsmall,
    hN, hunit, horth, heps, hw, hsupport, hrange, hsum, hwnear, hpos, ?_⟩
  intro tau htau htau_le
  obtain ⟨hemb, hcenter, hdomain, hmaps, hpatch⟩ := hcollar tau htau htau_le
  refine ⟨hemb, hcenter, hmaps, ?_, ?_⟩
  · intro i
    filter_upwards [hwnear i] with p hp
    exact hpatch i p hp
  · intro i p s hwne hs
    refine ⟨hsupport i (subset_tsupport (w i) hwne), ?_⟩
    have htime := (hdomain (p, s) ⟨mem_univ _, abs_lt.mp hs⟩).2
    apply abs_lt.mp
    simpa only [abs_mul, heps, one_mul] using (abs_lt.mpr htime)

end PoincareConjecture.M25.Topology3D
