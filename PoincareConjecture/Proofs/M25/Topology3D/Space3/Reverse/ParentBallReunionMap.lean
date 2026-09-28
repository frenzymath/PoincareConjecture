import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionReflection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionEndpoint











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem exists_reunion_axial_diffeomorph (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (d a lambda ε : ℝ) (ha : 0 < a) (had : a < d / 2)
    (hlambda : 0 < lambda) (hsmall : lambda * P.heightBound < a / 4)
    (hε : 0 < ε)
    (C : Set E3) (hC : IsCompact C)
    (havoid : Disjoint C (T '' (closedBall (0 : E2) 1 ×ˢ Ioo (-d) a))) :
    let F := fun q : UnitTwoSphere =>
      stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
        P.vertical P.vertical 1 (heightCoordinates (q : E3))
    let L := fun q : UnitTwoSphere => T ((F q).1, a + lambda * (F q).2)
    let B := fun q : UnitTwoSphere =>
      T ((F q).1, a + reunionAxialHeight a lambda ε 1 (F q).2)
    let Gamma := T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ))
    ∃ R : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ S : Set E3, IsCompact S ∧ S ⊆ T.target \ (C ∪ Gamma) ∧
        tsupport (fun y => R y - y) ⊆ S ∧
        tsupport (fun y => R.symm y - y) ⊆ S ∧
        (∀ y ∈ C ∪ Gamma, R y = y ∧ R.symm y = y) ∧
        ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 0 →
          R (L q) = B q ∧ R.symm (B q) = L q := by
  obtain ⟨D, _hD, e, hesource, hetarget, heq, _heiq, he, hei, heall⟩ :=
    exists_reunion_axial_chart P T hsource hT hTi a lambda ε ha hlambda hε
  obtain ⟨_hb, hmodels, _hstationary, hend, _hreflection, _hband⟩ :=
    reunion_reflected_model_spec P
  obtain ⟨_hg, _hderiv, _hbij, hbounds, _htail, hfixed, hzero, _hone⟩ :=
    reunionAxialHeight_spec a lambda ε ha hlambda hε
  let F := fun q : UnitTwoSphere =>
    stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical 1 (heightCoordinates (q : E3))
  let L := fun q : UnitTwoSphere => T ((F q).1, a + lambda * (F q).2)
  let B := fun q : UnitTwoSphere => T ((F q).1, a + reunionAxialHeight a lambda ε 1 (F q).2)
  let Gamma := T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ))
  have hFc : Continuous F :=
    (stackCapProfilePath_native_contMDiff P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical P.horizontal_smooth (reunionReflectedHorizontal_spec P).1
      P.vertical_smooth P.vertical_smooth).continuous.comp (continuous_const.prodMk continuous_id)
  have hzc : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  let K : Set E3 := Subtype.val ''
    {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let Moving : Set E3 := Subtype.val ''
    {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0 ∧ (F q).2 ≤ -ε / 2}
  have hMoving : IsCompact Moving :=
    (((isClosed_le hzc continuous_const).inter
      (isClosed_le hFc.snd continuous_const)).isCompact).image continuous_subtype_val
  have hMK : Moving ⊆ K := by
    rintro x ⟨q, hq, rfl⟩
    exact ⟨q, hq.1, rfl⟩
  have heSource : Icc (-1 : ℝ) 2 ×ˢ K ⊆ e.source := by
    rintro ⟨t, x⟩ ⟨_ht, q, _hq, rfl⟩
    exact heall t q
  have hstationary : ∀ x ∈ K \ Moving, ∀ t ∈ Icc (-1 : ℝ) 2,
      (e (t, x)).2 = (e (0, x)).2 := by
    rintro x ⟨⟨q, hq, rfl⟩, hmove⟩ t _ht
    have hz : -ε / 2 < (F q).2 := lt_of_not_ge (fun hZ => hmove ⟨q, ⟨hq, hZ⟩, rfl⟩)
    rw [heq, heq]
    change T ((F q).1, a + reunionAxialHeight a lambda ε t (F q).2) =
      T ((F q).1, a + reunionAxialHeight a lambda ε 0 (F q).2)
    rw [hfixed t (F q).2 hz.le, hzero]
  have hGammaSource : sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ) ⊆ T.source := by
    intro p hp
    exact hsource ⟨mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp hp.1).le,
      mem_univ _⟩
  have hGamma : IsCompact Gamma :=
    ((isCompact_sphere (0 : E2) 1).prod (isCompact_singleton (x := a))).image_of_continuousOn
      (T.continuousOn.mono hGammaSource)
  have hplaced (t : ℝ) (q : UnitTwoSphere) :
      ((F q).1, a + reunionAxialHeight a lambda ε t (F q).2) ∈ T.source :=
    hsource ⟨mem_closedBall_zero_iff.mpr (hmodels 1 q).1, mem_univ _⟩
  have hmoveAvoid : ∀ t ∈ Icc (-1 : ℝ) 2, ∀ x ∈ Moving,
      (e (t, x)).2 ∉ C ∪ Gamma := by
    rintro t _ht x ⟨q, hq, rfl⟩
    have hlow : -d < a + reunionAxialHeight a lambda ε t (F q).2 := by
      have hb := (hbounds t (F q).2).1
      have hm := mul_le_mul_of_nonneg_left (abs_le.mp (hend q)).1 hlambda.le
      nlinarith only [hb, hm, hsmall, ha, had]
    have hhigh : a + reunionAxialHeight a lambda ε t (F q).2 < a := by
      have hb := (hbounds t (F q).2).2
      have hm := mul_le_mul_of_nonneg_left hq.2 hlambda.le
      nlinarith only [hb, hm, mul_pos hlambda hε]
    rw [heq]
    change T ((F q).1, a + reunionAxialHeight a lambda ε t (F q).2) ∉ C ∪ Gamma
    intro hy
    rcases hy with hyC | hyGamma
    · exact Set.disjoint_left.mp havoid hyC
        ⟨((F q).1, a + reunionAxialHeight a lambda ε t (F q).2),
          ⟨mem_closedBall_zero_iff.mpr (hmodels 1 q).1, hlow, hhigh⟩, rfl⟩
    · rcases hyGamma with ⟨p, hp, hpEq⟩
      have hcoord := T.injOn (hGammaSource hp) (hplaced t q) hpEq
      have hheight := congrArg Prod.snd hcoord
      have hpa : p.2 = a := mem_singleton_iff.mp hp.2
      rw [hpa] at hheight
      exact (ne_of_lt hhigh) hheight.symm
  obtain ⟨Φ, S, _hΦ, _hΦi, _hΦzero, htrack, hSc, hSs, hs, his, _hfix, hprotected⟩ :=
    exists_protected_chart_evolution e he hei
      (fun p _hp => by simpa only using congrArg Prod.fst (heq p.1 p.2))
      K Moving (C ∪ Gamma)
      hMoving hMK (hC.isClosed.union hGamma.isClosed) heSource hstationary hmoveAvoid
  have hST : S ⊆ T.target \ (C ∪ Gamma) := by
    intro y hy
    obtain ⟨⟨p, hp, hpy⟩, hn⟩ := hSs hy
    rw [hetarget] at hp
    exact ⟨by rw [← hpy]; exact hp.2, hn⟩
  refine ⟨Φ 1, S, hSc, hST, hs 1, his 1, hprotected 1, ?_⟩
  intro q hq
  have h := htrack 1 (by norm_num) (q : E3) ⟨q, hq, rfl⟩
  simpa only [heq, Prod.snd, hzero, L, B, F] using h


theorem exists_reunion_diffeomorph (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (d a lambda : ℝ) (ha : 0 < a) (had : a < d / 2)
    (hlambda : 0 < lambda) (hsmall : lambda * P.heightBound < a / 4)
    (C : Set E3) (hC : IsCompact C)
    (havoid : Disjoint C (T '' (closedBall (0 : E2) 1 ×ˢ Ioo (-d) a))) :
    let cap := P.capMap T 0 1 a lambda ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let Gamma := T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ))
    let annulus := T '' (sphere (0 : E2) 1 ×ˢ Ioo (-a) a)
    let opposite := P.capMap T 0 (-1) a lambda ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ S : Set E3, IsCompact S ∧ S ⊆ T.target \ (C ∪ Gamma) ∧
        tsupport (fun y => G y - y) ⊆ S ∧
        tsupport (fun y => G.symm y - y) ⊆ S ∧
        (∀ y ∈ C ∪ Gamma, G y = y ∧ G.symm y = y) ∧
        G '' cap = Gamma ∪ annulus ∪ opposite ∧
        G.symm '' (Gamma ∪ annulus ∪ opposite) = cap := by
  obtain ⟨ε, hε, hεquarter, hband, _hcylinder⟩ :=
    (reunion_reflected_model_spec P).2.2.2.2.2
  obtain ⟨R0, S0, hS0, hS0where, hs0, his0, hfix0, htrack0⟩ :=
    exists_reunion_reflection_diffeomorph P T hsource hT hTi d a lambda
      ha had hlambda hsmall C hC havoid
  obtain ⟨R1, S1, hS1, hS1where, hs1, his1, hfix1, htrack1⟩ :=
    exists_reunion_axial_diffeomorph P T hsource hT hTi d a lambda ε
      ha had hlambda hsmall hε C hC havoid
  let G := R0.trans R1
  let S := S0 ∪ S1
  let F := fun q : UnitTwoSphere =>
    stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical 1 (heightCoordinates (q : E3))
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let cap := P.capMap T 0 1 a lambda '' Qminus
  let Gamma := T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ))
  let annulus := T '' (sphere (0 : E2) 1 ×ˢ Ioo (-a) a)
  let opposite := P.capMap T 0 (-1) a lambda ''
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  have hSc : IsCompact S := hS0.union hS1
  have hSwhere : S ⊆ T.target \ (C ∪ Gamma) := union_subset hS0where hS1where
  have hout (y : E3) (hy : y ∉ S) : G y = y ∧ G.symm y = y := by
    have h0 : R0 y = y := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun z : E3 => R0 z - z)
      (fun hm => hy (Or.inl (hs0 hm))))
    have hi0 : R0.symm y = y := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun z : E3 => R0.symm z - z)
      (fun hm => hy (Or.inl (his0 hm))))
    have h1 : R1 y = y := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun z : E3 => R1 z - z)
      (fun hm => hy (Or.inr (hs1 hm))))
    have hi1 : R1.symm y = y := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun z : E3 => R1.symm z - z)
      (fun hm => hy (Or.inr (his1 hm))))
    change R1 (R0 y) = y ∧ R0.symm (R1.symm y) = y
    rw [h0, h1, hi1, hi0]
    exact ⟨rfl, rfl⟩
  have hs : tsupport (fun y => G y - y) ⊆ S := by
    apply closure_minimal _ hSc.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hout y hn).1)
  have his : tsupport (fun y => G.symm y - y) ⊆ S := by
    apply closure_minimal _ hSc.isClosed
    intro y hy
    by_contra hn
    exact hy (sub_eq_zero.mpr (hout y hn).2)
  have hprotected (y : E3) (hy : y ∈ C ∪ Gamma) : G y = y ∧ G.symm y = y := by
    change R1 (R0 y) = y ∧ R0.symm (R1.symm y) = y
    rw [(hfix0 y hy).1, (hfix1 y hy).1, (hfix1 y hy).2, (hfix0 y hy).2]
    exact ⟨rfl, rfl⟩
  have htrack (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      G (P.capMap T 0 1 a lambda q) =
        T ((F q).1, a + reunionAxialHeight a lambda ε 1 (F q).2) := by
    change R1 (R0 (P.capMap T 0 1 a lambda q)) = _
    rw [(htrack0 q hq).1, (htrack1 q hq).1]
  have hfirst : G '' cap = T '' ((fun q : UnitTwoSphere =>
      ((F q).1, a + reunionAxialHeight a lambda ε 1 (F q).2)) '' Qminus) := by
    ext y
    constructor
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨_, ⟨q, hq, rfl⟩, (htrack q hq).symm⟩
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨P.capMap T 0 1 a lambda q, ⟨q, hq, rfl⟩, htrack q hq⟩
  have himage : G '' cap = Gamma ∪ annulus ∪ opposite := by
    rw [hfirst, reunion_axial_endpoint_image P a lambda ε ha hlambda hε hεquarter hband]
    rw [image_union, image_union]
    apply congrArg (fun V : Set E3 => Gamma ∪ annulus ∪ V)
    rw [image_image, image_image]
    apply image_congr
    intro q _hq
    change T ((P.model q).1, -a - lambda * (P.model q).2) =
      T ((P.model q).1, 0 + (-1) * (a + lambda * (P.model q).2))
    congr 1
    apply Prod.ext
    · rfl
    · ring
  refine ⟨G, S, hSc, hSwhere, hs, his, hprotected, himage, ?_⟩
  rw [← himage, image_image]
  change (fun y : E3 => G.symm (G y)) '' cap = cap
  simpa only [G.symm_apply_apply] using (image_id' cap)

end PoincareConjecture.M25.Topology3D
