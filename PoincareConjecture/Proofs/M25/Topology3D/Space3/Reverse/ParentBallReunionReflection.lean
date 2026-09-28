import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallProtectedEvolution
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionProfile
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileChart










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_reunion_reflection_diffeomorph (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (d a lambda : ℝ) (ha : 0 < a) (had : a < d / 2)
    (hlambda : 0 < lambda) (hsmall : lambda * P.heightBound < a / 4)
    (C : Set E3) (hC : IsCompact C)
    (havoid : Disjoint C (T '' (closedBall (0 : E2) 1 ×ˢ Ioo (-d) a))) :
    let M := stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical
    let L := fun q : UnitTwoSphere =>
      T ((M 1 (heightCoordinates (q : E3))).1,
        a + lambda * (M 1 (heightCoordinates (q : E3))).2)
    let Gamma := T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ))
    ∃ R : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ S : Set E3, IsCompact S ∧ S ⊆ T.target \ (C ∪ Gamma) ∧
        tsupport (fun y => R y - y) ⊆ S ∧
        tsupport (fun y => R.symm y - y) ⊆ S ∧
        (∀ y ∈ C ∪ Gamma, R y = y ∧ R.symm y = y) ∧
        ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 0 →
          R (P.capMap T 0 1 a lambda q) = L q ∧
          R.symm (L q) = P.capMap T 0 1 a lambda q := by
  obtain ⟨hA, hApos, _hAnear, _hAfar, hAbound, _hAnorth, _hAsouth, _hAoff⟩ :=
    reunionReflectedHorizontal_spec P
  obtain ⟨_hb, hmodels, hstationary, _hend, _hreflection, _hband⟩ :=
    reunion_reflected_model_spec P
  let M := stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
    P.vertical P.vertical
  let L := fun q : UnitTwoSphere => T ((M 1 (heightCoordinates (q : E3))).1,
    a + lambda * (M 1 (heightCoordinates (q : E3))).2)
  let Gamma := T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ))
  let e := stackPlacedProfileChart P.horizontal (reunionReflectedHorizontal P)
    P.vertical P.vertical P.horizontal_smooth hA P.vertical_smooth P.vertical_smooth
    P.horizontal_pos hApos P.vertical_pos P.vertical_pos T 0 1 a lambda one_ne_zero hlambda.ne'
  have he := stackPlacedProfileChart_contDiffOn P.horizontal (reunionReflectedHorizontal P)
    P.vertical P.vertical P.horizontal_smooth hA P.vertical_smooth P.vertical_smooth
    P.horizontal_pos hApos P.vertical_pos P.vertical_pos T 0 1 a lambda
    one_ne_zero hlambda.ne' hT hTi
  have heq (t : ℝ) (x : E3) :
      (e (t, x)).2 =
        T ((M t (heightCoordinates x)).1, a + lambda * (M t (heightCoordinates x)).2) := by
    change T ((M t (heightCoordinates x)).1, 0 + 1 * (a + lambda *
      (M t (heightCoordinates x)).2)) = _
    rw [zero_add, one_mul]
  have hetarget : e.target = univ ×ˢ T.target :=
    stackPlacedProfileChart_target _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hzc : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  let K : Set E3 := Subtype.val ''
    {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let Moving : Set E3 := Subtype.val ''
    {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ∈ Icc (-1 / 2 : ℝ) (-1 / 4)}
  have hMoving : IsCompact Moving :=
    ((isClosed_Icc.preimage hzc).isCompact).image continuous_subtype_val
  have hMK : Moving ⊆ K := by
    rintro x ⟨q, hq, rfl⟩
    exact ⟨q, hq.2.trans (by norm_num), rfl⟩
  have hplaced (t : ℝ) (q : UnitTwoSphere) :
      ((M t (heightCoordinates (q : E3))).1,
        a + lambda * (M t (heightCoordinates (q : E3))).2) ∈ T.source :=
    hsource ⟨mem_closedBall_zero_iff.mpr (hmodels t q).1, mem_univ _⟩
  have heSource : Icc (-1 : ℝ) 2 ×ˢ K ⊆ e.source := by
    rintro ⟨t, x⟩ ⟨_ht, q, _hq, rfl⟩
    rw [stackPlacedProfileChart_source]
    change ((M t (heightCoordinates (q : E3))).1,
      0 + 1 * (a + lambda * (M t (heightCoordinates (q : E3))).2)) ∈ T.source
    simpa only [zero_add, one_mul] using hplaced t q
  have hfixed : ∀ x ∈ K \ Moving, ∀ t ∈ Icc (-1 : ℝ) 2,
      (e (t, x)).2 = (e (0, x)).2 := by
    rintro x ⟨⟨q, _hq, rfl⟩, hmove⟩ t _ht
    have hoff : (heightCoordinates (q : E3)).2 ∉ Icc (-1 / 2 : ℝ) (-1 / 4) :=
      fun hq => hmove ⟨q, hq, rfl⟩
    have hMt : M t (heightCoordinates (q : E3)) = M 0 (heightCoordinates (q : E3)) :=
      hstationary t (heightCoordinates (q : E3)) hoff
    rw [heq, heq, hMt]
  have hGammaSource : sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ) ⊆ T.source := by
    intro p hp
    exact hsource ⟨mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp hp.1).le,
      mem_univ _⟩
  have hGamma : IsCompact Gamma :=
    ((isCompact_sphere (0 : E2) 1).prod (isCompact_singleton (x := a))).image_of_continuousOn
      (T.continuousOn.mono hGammaSource)
  have hmoveAvoid : ∀ t ∈ Icc (-1 : ℝ) 2, ∀ x ∈ Moving,
      (e (t, x)).2 ∉ C ∪ Gamma := by
    rintro t _ht x ⟨q, hq, rfl⟩
    have hz : (M t (heightCoordinates (q : E3))).2 < 0 :=
      (stackCapProfilePath_snd_neg_iff P.horizontal (reunionReflectedHorizontal P)
        P.vertical P.vertical P.vertical_pos P.vertical_pos t
        (heightCoordinates (q : E3))).mpr (by linarith only [hq.2])
    have hlow : -d < a + lambda * (M t (heightCoordinates (q : E3))).2 := by
      have hh := mul_le_mul_of_nonneg_left (abs_le.mp (hmodels t q).2).1 hlambda.le
      nlinarith only [hh, hsmall, ha, had]
    have hhigh : a + lambda * (M t (heightCoordinates (q : E3))).2 < a := by
      have hh := mul_neg_of_pos_of_neg hlambda hz
      linarith only [hh]
    rw [heq]
    intro hy
    rcases hy with hyC | hyGamma
    · exact Set.disjoint_left.mp havoid hyC
        ⟨((M t (heightCoordinates (q : E3))).1,
          a + lambda * (M t (heightCoordinates (q : E3))).2),
          ⟨mem_closedBall_zero_iff.mpr (hmodels t q).1, hlow, hhigh⟩, rfl⟩
    · rcases hyGamma with ⟨p, hp, hpEq⟩
      have hcoord := T.injOn (hGammaSource hp) (hplaced t q) hpEq
      have hheight := congrArg Prod.snd hcoord
      have hpa : p.2 = a := mem_singleton_iff.mp hp.2
      rw [hpa] at hheight
      exact (ne_of_lt hhigh) hheight.symm
  obtain ⟨Φ, S, _hΦ, _hΦi, _hΦzero, htrack, hSc, hSs, hs, his, _hfix, hprotected⟩ :=
    exists_protected_chart_evolution e he.1 he.2 (fun _ _ => rfl)
      K Moving (C ∪ Gamma) hMoving hMK (hC.isClosed.union hGamma.isClosed)
      heSource hfixed hmoveAvoid
  have hST : S ⊆ T.target \ (C ∪ Gamma) := by
    intro y hy
    obtain ⟨⟨p, hp, hpy⟩, hn⟩ := hSs hy
    rw [hetarget] at hp
    exact ⟨by rw [← hpy]; exact hp.2, hn⟩
  refine ⟨Φ 1, S, hSc, hST, hs 1, his 1, hprotected 1, ?_⟩
  intro q hq
  have hzero : (e (0, (q : E3))).2 = P.capMap T 0 1 a lambda q :=
    (stackPlacedProfileCap_endpoints P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical P.horizontal_smooth hA P.vertical_smooth P.vertical_smooth
      P.horizontal_pos hApos P.vertical_pos P.vertical_pos T 0 1 a lambda q).1
  have h := htrack 1 (by norm_num) (q : E3) ⟨q, hq, rfl⟩
  rw [hzero, heq] at h
  exact h

end PoincareConjecture.M25.Topology3D
