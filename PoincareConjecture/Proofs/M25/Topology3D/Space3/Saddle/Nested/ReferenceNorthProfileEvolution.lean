import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCanonicalProfiles
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_north_profile_evolution_in_height_strip
    (P : SurgeryCapProfile) :
    let ac := stackCanonicalHorizontal (1 / 4) (1 / 2)
    let bc := stackCanonicalVertical (1 / 4) (1 / 2)
    let Mc := stackCapProfilePath ac ac bc bc 0
    ∃ B0 : ℝ, 1 ≤ B0 ∧
      ∀ (T : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) (E2 × ℝ) E3 ∞)
        (s lambda eta : ℝ),
        (∀ p : E2 × ℝ, (heightCoordinates (T p)).2 = p.2) →
        0 < lambda → 0 < eta → lambda * B0 < eta →
        let Qplus : Set UnitTwoSphere :=
          {q | 0 ≤ (heightCoordinates (q : E3)).2}
        let cap0 : UnitTwoSphere → E3 := fun q =>
          let m := Mc (heightCoordinates (q : E3))
          T (m.1, s + lambda * m.2)
        let cap1 : UnitTwoSphere → E3 := fun q =>
          T ((P.model q).1, s + lambda * (P.model q).2)
        ∃ (O : Set E3)
          (Psi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
          (K : Set E3),
          IsOpen O ∧ T '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆ O ∧
          ContDiff ℝ ∞ (fun p : ℝ × E3 => Psi p.1 p.2) ∧
          ContDiff ℝ ∞ (fun p : ℝ × E3 => (Psi p.1).symm p.2) ∧
          (∀ y : E3, Psi 0 y = y) ∧
          (∀ q ∈ Qplus, Psi 1 (cap0 q) = cap1 q) ∧
          Psi 1 '' (cap0 '' Qplus) = cap1 '' Qplus ∧
          (Psi 1).symm '' (cap1 '' Qplus) = cap0 '' Qplus ∧
          IsCompact K ∧
          K ⊆ {y : E3 | s < (heightCoordinates y).2 ∧
            (heightCoordinates y).2 < s + eta} \ O ∧
          (∀ t : ℝ, tsupport (fun y : E3 => Psi t y - y) ⊆ K) ∧
          (∀ t : ℝ, tsupport (fun y : E3 => (Psi t).symm y - y) ⊆ K) ∧
          (∀ (t : ℝ) (y : E3), y ∉ K → Psi t y = y ∧ (Psi t).symm y = y) ∧
          (∀ (t : ℝ) (y : E3), y ∈ O → Psi t y = y ∧ (Psi t).symm y = y) ∧
          (∀ (t : ℝ) (y : E3), (heightCoordinates y).2 ≤ s →
            Psi t y = y ∧ (Psi t).symm y = y) := by
  classical
  dsimp only
  let ac := stackCanonicalHorizontal (1 / 4) (1 / 2)
  let bc := stackCanonicalVertical (1 / 4) (1 / 2)
  obtain ⟨hac, hacpos, _, hacbound, hacnear, _, _⟩ :=
    stackCanonicalHorizontal_spec (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hbc, hbcpos, _, _, hbcfar, _⟩ :=
    stackCanonicalVertical_spec (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  let a0 : ℝ → ℝ := fun v => ac (-v)
  let a1 : ℝ → ℝ := fun v => P.horizontal (-v)
  have ha0 : ContDiff ℝ ∞ a0 := hac.comp contDiff_id.neg
  have ha1 : ContDiff ℝ ∞ a1 := P.horizontal_smooth.comp contDiff_id.neg
  have hapos0 (v : ℝ) : 0 < a0 v := hacpos (-v)
  have hapos1 (v : ℝ) : 0 < a1 v := P.horizontal_pos (-v)
  have habound0 (v : ℝ) (hv : |v| < 1) : a0 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹ := by
    simpa only [a0, neg_sq] using hacbound (-v) (by simpa only [abs_neg] using hv)
  have habound1 (v : ℝ) (hv : |v| < 1) : a1 v ≤ (Real.sqrt (1 - v ^ 2))⁻¹ := by
    simpa only [a1, neg_sq] using P.horizontal_bound (-v) (by simpa only [abs_neg] using hv)
  have hanear0 (v : ℝ) (hv : |v| < 1 / 8) : a0 v = (Real.sqrt (1 - v ^ 2))⁻¹ := by
    simpa only [a0, neg_sq] using hacnear (-v) (by rw [abs_neg]; linarith)
  have hanear1 (v : ℝ) (hv : |v| < 1 / 8) : a1 v = (Real.sqrt (1 - v ^ 2))⁻¹ := by
    simpa only [a1, neg_sq] using P.horizontal_near (-v) (by rw [abs_neg]; linarith)
  let W : Set E2 := {x | 3 / 4 < ‖x‖}
  have hW : IsOpen W := isOpen_lt continuous_const continuous_norm
  have hcircle : sphere (0 : E2) 1 ⊆ W := by
    intro x hx
    change 3 / 4 < ‖x‖
    rw [mem_sphere_zero_iff_norm.mp hx]
    norm_num
  have hbnear0 (x : E2) (hx : x ∈ W) : bc x = 1 := hbcfar x (by
    change 3 / 4 < ‖x‖ at hx
    linarith)
  have hbnear1 (x : E2) (hx : x ∈ W) : P.vertical x = 1 := P.vertical_far x (by
    change 3 / 4 < ‖x‖ at hx
    linarith)
  obtain ⟨B0, hB0, hbound⟩ := exists_stackCapProfilePath_height_bound
    a0 a1 bc P.vertical ha0 ha1 hbc P.vertical_smooth
  refine ⟨B0, hB0, ?_⟩
  intro T s lambda eta hheight hlambda heta hsmall
  let Tp := T.toHomeomorph.toOpenPartialHomeomorph
  have hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ Tp.source := by
    intro p _hp
    exact mem_univ p
  have hT : ContDiffOn ℝ ∞ Tp Tp.source := T.contMDiff_toFun.contDiff.contDiffOn
  have hTi : ContDiffOn ℝ ∞ Tp.symm Tp.target := T.contMDiff_invFun.contDiff.contDiffOn
  have hv : ‖heightCoordinates.symm ((0 : E2), (1 : ℝ))‖ = 1 := by
    have hh := heightCoordinates_symm_norm_sq ((0 : E2), (1 : ℝ))
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), one_pow, zero_add] at hh
    nlinarith [norm_nonneg (heightCoordinates.symm ((0 : E2), (1 : ℝ)))]
  let u : UnitTwoSphere := ⟨heightCoordinates.symm (0, 1),
    mem_sphere_zero_iff_norm.mpr hv⟩
  have hu (y : E3) : inner ℝ (u : E3) y = (heightCoordinates y).2 := by
    change inner ℝ (heightCoordinates.symm ((0 : E2), (1 : ℝ))) y = _
    simp only [heightCoordinates_symm_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_three, heightCoordinates_snd_apply]
    simp
  have hheight' (p : E2 × ℝ) (_hp : p ∈ Tp.source) : inner ℝ (u : E3) (Tp p) = p.2 := by
    rw [hu]
    exact hheight p
  obtain ⟨O, Psi, K, hO, hrim, _hOt, hPsi, hPsii, hzero, htrack, _himage,
      hK, hKs, hsupp, hisupp, hfix, hfixO, hfixIn⟩ :=
    exists_stackPlacedProfileEvolution_in_height_strip
      a0 a1 bc P.vertical ha0 ha1 hbc P.vertical_smooth
      hapos0 hapos1 hbcpos P.vertical_pos habound0 habound1
      Tp hsource hT hTi u hheight' s (-1) 0 lambda (by norm_num) hlambda
      (1 / 8) (by norm_num) W hW hcircle hanear0 hanear1 hbnear0 hbnear1
      B0 eta hB0 hbound heta hsmall
  let reflected : UnitTwoSphere → UnitTwoSphere := fun q =>
    ⟨heightCoordinates.symm ((heightCoordinates (q : E3)).1,
      -(heightCoordinates (q : E3)).2), mem_sphere_zero_iff_norm.mpr (by
        have hq := sphere_height_coordinates_sq q
        have hh := heightCoordinates_symm_norm_sq
          ((heightCoordinates (q : E3)).1, -(heightCoordinates (q : E3)).2)
        simp only [neg_sq] at hh
        nlinarith [norm_nonneg (heightCoordinates.symm
          ((heightCoordinates (q : E3)).1, -(heightCoordinates (q : E3)).2))])⟩
  have hreflected (q : UnitTwoSphere) : heightCoordinates (reflected q : E3) =
      ((heightCoordinates (q : E3)).1, -(heightCoordinates (q : E3)).2) :=
    heightCoordinates.apply_symm_apply _
  let cap0 : UnitTwoSphere → E3 := fun q =>
    let m := stackCapProfilePath ac ac bc bc 0 (heightCoordinates (q : E3))
    T (m.1, s + lambda * m.2)
  let cap1 : UnitTwoSphere → E3 := fun q =>
    T ((P.model q).1, s + lambda * (P.model q).2)
  have hcap0 (q : UnitTwoSphere) :
      stackPlacedProfileCap a0 a1 bc P.vertical Tp s (-1) 0 lambda 0 (reflected q) =
        cap0 q := by
    simp only [stackPlacedProfileCap, hreflected, cap0, stackCapProfilePath,
      stackProfileBlend_of_nonpos a0 a1 0 le_rfl,
      stackProfileBlend_of_nonpos bc P.vertical 0 le_rfl,
      stackProfileBlend_of_nonpos ac ac 0 le_rfl,
      stackProfileBlend_of_nonpos bc bc 0 le_rfl, a0, neg_neg]
    change T (_, _) = T (_, _)
    congr 1
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hcap1 (q : UnitTwoSphere) :
      stackPlacedProfileCap a0 a1 bc P.vertical Tp s (-1) 0 lambda 1 (reflected q) =
        cap1 q := by
    simp only [stackPlacedProfileCap, hreflected, cap1, stackCapProfilePath,
      stackProfileBlend_of_one_le a0 a1 1 le_rfl,
      stackProfileBlend_of_one_le bc P.vertical 1 le_rfl, a1, neg_neg,
      SurgeryCapProfile.model, surgeryCapModel, flatCapDiffeomorph_apply]
    change T (_, _) = T (_, _)
    congr 1
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hpoint (q : UnitTwoSphere) (hq : 0 ≤ (heightCoordinates (q : E3)).2) :
      Psi 1 (cap0 q) = cap1 q := by
    have hr : (heightCoordinates (reflected q : E3)).2 ≤ 0 := by
      rw [hreflected]
      exact neg_nonpos.mpr hq
    simpa only [hcap0, hcap1] using htrack 1 (by norm_num) (reflected q) hr
  let Qplus : Set UnitTwoSphere := {q | 0 ≤ (heightCoordinates (q : E3)).2}
  have hforward : Psi 1 '' (cap0 '' Qplus) = cap1 '' Qplus := by
    ext y
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (hpoint q hq).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨cap0 q, ⟨q, hq, rfl⟩, hpoint q hq⟩
  have hback (q : UnitTwoSphere) (hq : q ∈ Qplus) :
      (Psi 1).symm (cap1 q) = cap0 q := by
    rw [← hpoint q hq]
    exact (Psi 1).symm_apply_apply _
  have hinverse : (Psi 1).symm '' (cap1 '' Qplus) = cap0 '' Qplus := by
    ext y
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (hback q hq).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨cap1 q, ⟨q, hq, rfl⟩, hback q hq⟩
  have hKs' : K ⊆ {y : E3 | s < (heightCoordinates y).2 ∧
      (heightCoordinates y).2 < s + eta} \ O := by
    intro y hy
    rcases hKs hy with ⟨⟨⟨_hyT, hyabs⟩, hyout⟩, hyO⟩
    change |inner ℝ (u : E3) y - (s + -1 * 0)| < eta at hyabs
    change -1 * (inner ℝ (u : E3) y - (s + -1 * 0)) < 0 at hyout
    rw [hu] at hyabs hyout
    simp only [mul_zero, add_zero] at hyabs hyout
    refine ⟨⟨by linarith, ?_⟩, hyO⟩
    linarith [(abs_lt.mp hyabs).2]
  refine ⟨O, Psi, K, hO, ?_, hPsi, hPsii, hzero, hpoint, hforward, hinverse,
    hK, hKs', hsupp, hisupp, hfix, hfixO, ?_⟩
  · change (T : E2 × ℝ → E3) ''
      (sphere (0 : E2) 1 ×ˢ ({s + -1 * 0} : Set ℝ)) ⊆ O at hrim
    simpa only [mul_zero, add_zero] using hrim
  · intro t y hy
    apply hfixIn t y
    change 0 ≤ -1 * (inner ℝ (u : E3) y - (s + -1 * 0))
    rw [hu]
    simp only [mul_zero, add_zero]
    linarith

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
