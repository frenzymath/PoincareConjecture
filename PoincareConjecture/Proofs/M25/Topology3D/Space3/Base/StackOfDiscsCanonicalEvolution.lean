import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag









set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


theorem exists_stackCanonicalProfile_common_germ
    (P : SurgeryCapProfile) (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let delta := min v0 (1 / 4)
    let W := {x : E2 | max rOne (1 / 2) < ‖x‖}
    0 < delta ∧ IsOpen W ∧ sphere (0 : E2) 1 ⊆ W ∧
    (∀ v, |v| < delta → P.horizontal v = (Real.sqrt (1 - v ^ 2))⁻¹) ∧
    (∀ v, |v| < delta → a v = (Real.sqrt (1 - v ^ 2))⁻¹) ∧
    (∀ x ∈ W, P.vertical x = 1) ∧
    (∀ x ∈ W, b x = 1) ∧
    ∃ O : Set (E2 × ℝ), IsOpen O ∧
      sphere (0 : E2) 1 ×ˢ ({0} : Set ℝ) ⊆ O ∧
      (∀ t : ℝ, ∀ p ∈ O,
        stackCapProfilePath P.horizontal a P.vertical b t p =
          ((Real.sqrt (1 - p.2 ^ 2))⁻¹ • p.1, p.2)) ∧
      ∀ t : ℝ, ∀ p ∈ O,
        stackCapProfilePath P.horizontal a P.vertical b t p =
          stackCapProfilePath P.horizontal a P.vertical b 0 p := by
  dsimp only
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let delta := min v0 (1 / 4)
  let W := {x : E2 | max rOne (1 / 2) < ‖x‖}
  obtain ⟨_, _, _, _, hanear, _, _⟩ := stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨_, _, _, _, hbfar, _⟩ := stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  have hdelta : 0 < delta := lt_min hv0 (by norm_num)
  have hW : IsOpen W := isOpen_lt continuous_const continuous_norm
  have hcircle : sphere (0 : E2) 1 ⊆ W := by
    intro x hx
    change max rOne (1 / 2) < ‖x‖
    rw [mem_sphere_zero_iff_norm.mp hx]
    exact max_lt hrOne (by norm_num)
  have ha0near : ∀ v, |v| < delta → P.horizontal v = (Real.sqrt (1 - v ^ 2))⁻¹ :=
    fun v hv => P.horizontal_near v (hv.le.trans (min_le_right _ _))
  have ha1near : ∀ v, |v| < delta → a v = (Real.sqrt (1 - v ^ 2))⁻¹ :=
    fun v hv => hanear v (hv.le.trans (min_le_left _ _))
  have hb0near : ∀ x ∈ W, P.vertical x = 1 :=
    fun x hx => P.vertical_far x ((le_max_right _ _).trans hx.le)
  have hb1near : ∀ x ∈ W, b x = 1 :=
    fun x hx => hbfar x ((le_max_left _ _).trans hx.le)
  refine ⟨hdelta, hW, hcircle, ha0near, ha1near, hb0near, hb1near, ?_⟩
  exact exists_stackCapProfilePath_common_ambient_germ P.horizontal a P.vertical b
    delta hdelta W hW hcircle ha0near ha1near hb0near hb1near


theorem exists_stackCanonicalProfile_small_scale
    (P : SurgeryCapProfile) (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (lambda0 eta : ℝ) (hlambda0 : 0 < lambda0) (heta : 0 < eta) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    ∃ B lambda : ℝ, 1 ≤ B ∧ 0 < lambda ∧ lambda < lambda0 ∧
      lambda * B < eta ∧
      ∀ t : ℝ, ∀ q : UnitTwoSphere,
        |(stackCapProfilePath P.horizontal a P.vertical b t
          (heightCoordinates (q : E3))).2| ≤ B := by
  dsimp only
  obtain ⟨ha, _, _, _, _, _, _⟩ := stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨hb, _, _, _, _, _⟩ := stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  obtain ⟨B, hB, hbound⟩ := exists_stackCapProfilePath_height_bound
    P.horizontal (stackCanonicalHorizontal v0 v1) P.vertical (stackCanonicalVertical rFlat rOne)
    P.horizontal_smooth ha P.vertical_smooth hb
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let lambda := min lambda0 (eta / B) / 2
  have hlambda : 0 < lambda := div_pos (lt_min hlambda0 (div_pos heta hBpos)) (by norm_num)
  have hsmall0 : lambda < lambda0 := by
    have hmin : min lambda0 (eta / B) ≤ lambda0 := min_le_left _ _
    dsimp only [lambda]
    linarith
  have hsmall : lambda * B < eta := by
    have hmin : min lambda0 (eta / B) ≤ eta / B := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hmin hBpos.le
    rw [div_mul_cancel₀ _ hBpos.ne'] at hmul
    dsimp only [lambda]
    nlinarith
  exact ⟨B, lambda, hB, hlambda, hsmall0, hsmall, hbound⟩


theorem exists_stackCanonicalProfileEvolution
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (tag : SurgeryCapTag psi u) (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1)
    (gammaMatch gammaGraph : ℝ)
    (hgammaMatch : 0 < gammaMatch) (hgammaGraph : 0 < gammaGraph) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let seam := tag.cutHeight + tag.sign * tag.removal
    let chi := fun y : E3 => tag.sign * (inner ℝ (u : E3) y - seam)
    let eta := min gammaMatch (min gammaGraph (tag.removal / 2)) / 2
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    ∃ B lambda : ℝ,
      let cap := stackPlacedProfileCap tag.profile.horizontal a
        tag.profile.vertical b tag.tube tag.cutHeight tag.sign tag.removal lambda
      1 ≤ B ∧ 0 < lambda ∧ lambda < tag.scale ∧ lambda * B < eta ∧
      (∀ t : ℝ, ∀ q : UnitTwoSphere,
        |(stackCapProfilePath tag.profile.horizontal a tag.profile.vertical b t
          (heightCoordinates (q : E3))).2| ≤ B) ∧
      ∃ N : Set E3,
      ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ K : Set E3,
        IsOpen N ∧
        tag.tube '' (sphere (0 : E2) 1 ×ˢ ({seam} : Set ℝ)) ⊆ N ∧
        N ⊆ tag.tube.target ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
        (∀ y, Phi 0 y = y) ∧
        (∀ t ∈ Ioo (-1 : ℝ) 2, ∀ q ∈ Qminus,
          Phi t (cap 0 q) = cap t q) ∧
        (∀ t ∈ Ioo (-1 : ℝ) 2,
          Phi t '' (cap 0 '' Qminus) = cap t '' Qminus) ∧
        (∀ q ∈ Qminus,
          Phi 1 (tag.profile.capMap tag.tube tag.cutHeight tag.sign
            tag.removal lambda q) =
              tag.tube ((M (heightCoordinates (q : E3))).1,
                tag.cutHeight + tag.sign *
                  (tag.removal + lambda * (M (heightCoordinates (q : E3))).2))) ∧
        (∀ q ∈ Qminus, -lambda ≤ chi (cap 1 q) ∧ chi (cap 1 q) ≤ 0) ∧
        IsCompact K ∧
        K ⊆ ((tag.tube.target ∩
          {y | |inner ℝ (u : E3) y - seam| < eta}) ∩
          {y | chi y < 0}) \ N ∧
        (∀ t, tsupport (fun y => Phi t y - y) ⊆ K) ∧
        (∀ t, tsupport (fun y => (Phi t).symm y - y) ⊆ K) ∧
        (∀ t y, y ∉ K → Phi t y = y ∧ (Phi t).symm y = y) ∧
        (∀ t y, y ∈ N → Phi t y = y ∧ (Phi t).symm y = y) ∧
        ∀ t y, 0 ≤ chi y → Phi t y = y ∧ (Phi t).symm y = y := by
  dsimp only
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let seam := tag.cutHeight + tag.sign * tag.removal
  let chi := fun y : E3 => tag.sign * (inner ℝ (u : E3) y - seam)
  let eta := min gammaMatch (min gammaGraph (tag.removal / 2)) / 2
  have heta : 0 < eta := div_pos
    (lt_min hgammaMatch (lt_min hgammaGraph (div_pos tag.removal_pos (by norm_num))))
    (by norm_num)
  obtain ⟨B, lambda, hB, hlambda, hsmall0, hsmall, hbound⟩ :=
    exists_stackCanonicalProfile_small_scale tag.profile rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1 tag.scale eta tag.scale_pos heta
  let cap := stackPlacedProfileCap tag.profile.horizontal a tag.profile.vertical b
    tag.tube tag.cutHeight tag.sign tag.removal lambda
  obtain ⟨ha, hapos, _, habound, _, _, _⟩ :=
    stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1
  obtain ⟨hb, hbpos, _, _, _, _⟩ :=
    stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne
  obtain ⟨hdelta, hW, hcircle, ha0near, ha1near, hb0near, hb1near, _⟩ :=
    exists_stackCanonicalProfile_common_germ tag.profile rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1
  obtain ⟨N, Phi, K, hN, hseam, hNt, hPhi, hPhii, hzero, htrack, himage,
      hK, hKs, hs, his, hfix, hfixN, hfixIn⟩ :=
    exists_stackPlacedProfileEvolution_in_height_strip tag.profile.horizontal a
      tag.profile.vertical b tag.profile.horizontal_smooth ha tag.profile.vertical_smooth hb
      tag.profile.horizontal_pos hapos tag.profile.vertical_pos hbpos
      tag.profile.horizontal_bound habound tag.tube tag.tube_source tag.tube_smooth
      tag.tube_inverse u tag.tube_height tag.cutHeight tag.sign tag.removal lambda
      tag.sign_abs hlambda (min v0 (1 / 4)) hdelta
      {x : E2 | max rOne (1 / 2) < ‖x‖} hW hcircle
      ha0near ha1near hb0near hb1near B eta hB hbound heta hsmall
  have hMone (p : E2 × ℝ) :
      stackCapProfilePath tag.profile.horizontal a tag.profile.vertical b 1 p = M p := by
    simp only [M, stackCapProfilePath,
      stackProfileBlend_of_one_le tag.profile.horizontal a 1 le_rfl,
      stackProfileBlend_of_one_le tag.profile.vertical b 1 le_rfl,
      stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  have hcapzero (q : UnitTwoSphere) :
      cap 0 q = tag.profile.capMap tag.tube tag.cutHeight tag.sign tag.removal lambda q :=
    (stackPlacedProfileCap_endpoints tag.profile.horizontal a tag.profile.vertical b
      tag.profile.horizontal_smooth ha tag.profile.vertical_smooth hb
      tag.profile.horizontal_pos hapos tag.profile.vertical_pos hbpos
      tag.tube tag.cutHeight tag.sign tag.removal lambda q).1
  have hcapone (q : UnitTwoSphere) : cap 1 q =
      tag.tube ((M (heightCoordinates (q : E3))).1,
        tag.cutHeight + tag.sign *
          (tag.removal + lambda * (M (heightCoordinates (q : E3))).2)) := by
    change tag.tube _ = tag.tube _
    simp only [hMone]
  refine ⟨B, lambda, hB, hlambda, hsmall0, hsmall, hbound,
    N, Phi, K, hN, hseam, hNt, hPhi, hPhii, hzero, htrack, himage, ?_, ?_,
    hK, hKs, hs, his, hfix, hfixN, hfixIn⟩
  · intro q hq
    have h := htrack 1 (by norm_num) q hq
    change Phi 1 (cap 0 q) = cap 1 q at h
    rw [hcapzero, hcapone] at h
    exact h
  · intro q hq
    have hh : chi (cap 1 q) = lambda * (M (heightCoordinates (q : E3))).2 := by
      have h := stackPlacedProfileCap_signed_height tag.profile.horizontal a
        tag.profile.vertical b tag.profile.horizontal_smooth ha tag.profile.vertical_smooth hb
        tag.profile.horizontal_pos hapos tag.profile.vertical_pos hbpos
        tag.tube tag.cutHeight tag.sign tag.removal lambda
        tag.profile.horizontal_bound habound tag.tube_source u tag.tube_height tag.sign_abs 1 q
      simpa only [hMone] using h
    obtain ⟨_, _, hlo, hhi, _, _⟩ := stackCanonicalModel_southern_geometry
      rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hgap
      (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q) hq
    change -lambda ≤ chi (cap 1 q) ∧ chi (cap 1 q) ≤ 0
    rw [hh]
    constructor
    · have h := mul_le_mul_of_nonneg_left hlo hlambda.le
      simpa only [mul_neg, mul_one] using h
    · exact mul_nonpos_of_nonneg_of_nonpos hlambda.le hhi

end PoincareConjecture.M25.Topology3D
