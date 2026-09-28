import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.TwoProfileEndBall
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_lower_tube_end_ball_with_retained_cylinder
    (Pm P : SurgeryCapProfile) (u : UnitTwoSphere)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p ∈ T.source, ⟪(u : E3), T p⟫_ℝ = p.2)
    (ell top lm lambda z : ℝ) (horder : ell < top)
    (hlm : 0 < lm) (hlambda : 0 < lambda) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let lower := (fun q : UnitTwoSphere =>
      T ((Pm.model q).1, ell + lm * (Pm.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let E := lower ∪ T '' (sphere (0 : E2) 1 ×ˢ Icc ell top)
    let north := (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let L := T '' (sphere (0 : E2) 1 ×ˢ Icc top z)
    ∃ (Q : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
      (A : BallNeighborhoodChart E3 E3) (ov : ℝ),
      0 < ov ∧ ov < 1 / 4 ∧
      A.chart = Q.toHomeomorph.toOpenPartialHomeomorph.trans T ∧
      A.chart.source = Q ⁻¹' T.source ∧ A.chart.target = T.target ∧
      (∀ y : E3, A.chart y = T (Q y)) ∧
      (∀ y : E3, A.chart.symm y = Q.symm (T.symm y)) ∧
      A.boundary = E ∪ north ∧
      A.inside ⊆ T '' (ball (0 : E2) 1 ×ˢ (univ : Set ℝ)) ∧
      A.closedRegion ⊆ T '' (closedBall (0 : E2) 1 ×ˢ
        Icc (ell - lm * Pm.heightBound) (top + lambda * P.heightBound)) ∧
      (∀ s ∈ Icc ell top,
        A.inside ∩ {y : E3 | H y = s} =
          T '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
        A.closedRegion ∩ {y : E3 | H y = s} =
          T '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ))) ∧
      (∀ q : UnitTwoSphere, -ov < (heightCoordinates (q : E3)).2 →
        T ((P.model q).1, top + lambda * (P.model q).2) ∈ A.boundary) ∧
      E ∩ north = T '' (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ)) ∧
      Disjoint A.inside L ∧ A.closedRegion ∩ L ⊆ north := by
  classical
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  change ∀ p ∈ T.source, H (T p) = p.2 at hheight
  let lower := (fun q : UnitTwoSphere =>
    T ((Pm.model q).1, ell + lm * (Pm.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let E := lower ∪ T '' (sphere (0 : E2) 1 ×ˢ Icc ell top)
  let north := (fun q : UnitTwoSphere =>
    T ((P.model q).1, top + lambda * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let L := T '' (sphere (0 : E2) 1 ×ˢ Icc top z)
  let rim := T '' (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ))
  obtain ⟨Q, A, ov, hov, hov1, hchart, hs, ht, hp, hi, hb, hAi, hAc, hcuts, hpatch⟩ :=
    exists_two_profile_end_ball Pm P u T hsource hT hTi hheight ell top lm lambda
      horder hlm hlambda
  have hn : (fun y : E3 => T
      ((flatCapDiffeomorph P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
        (fun s => (P.horizontal_pos s).ne') (fun x => (P.vertical_pos x).ne')
          (heightCoordinates y)).1,
        top + lambda * (flatCapDiffeomorph P.horizontal P.vertical
          P.horizontal_smooth P.vertical_smooth (fun s => (P.horizontal_pos s).ne')
            (fun x => (P.vertical_pos x).ne') (heightCoordinates y)).2)) ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} = north := by
    ext y
    constructor
    · rintro ⟨q, ⟨hqn, hqh⟩, rfl⟩
      exact ⟨⟨q, mem_sphere_zero_iff_norm.mpr hqn⟩, hqh, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, rfl⟩
  have hAb : A.boundary = E ∪ north := by
    rw [hb, hn]
  have hlower (y : E3) (hy : y ∈ lower) : H y < top := by
    obtain ⟨q, hq, rfl⟩ := hy
    rw [hheight ((Pm.model q).1, ell + lm * (Pm.model q).2) (hsource
      ⟨mem_closedBall_zero_iff.mpr (Pm.model_fst_norm_le q), mem_univ _⟩)]
    have hm : (Pm.model q).2 ≤ 0 := by
      change Pm.vertical _ * (heightCoordinates (q : E3)).2 ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (Pm.vertical_pos _).le hq
    exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hlm.le hm)).trans_lt horder
  have hEh (y : E3) (hy : y ∈ E) : H y ≤ top := by
    rcases hy with hy | ⟨p, hp, rfl⟩
    · exact (hlower y hy).le
    · rw [hheight p (hsource ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)]
      exact hp.2.2
  have hElevel : E ∩ {y : E3 | H y = top} = rim := by
    ext y
    constructor
    · rintro ⟨hyE, hyH⟩
      rcases hyE with hy | ⟨p, hp, rfl⟩
      · exact False.elim ((ne_of_lt (hlower y hy)) hyH)
      · have hpt : p.2 = top :=
          (hheight p (hsource ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)).symm.trans hyH
        exact ⟨p, ⟨hp.1, hpt⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hpt : p.2 = top := hp.2
      refine ⟨Or.inr ⟨p, ⟨hp.1, ?_⟩, rfl⟩, ?_⟩
      · rw [hpt]
        exact ⟨horder.le, le_rfl⟩
      · exact (hheight p (hsource ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)).trans hpt
  have hNh (y : E3) (hy : y ∈ north) : top ≤ H y := by
    obtain ⟨q, hq, rfl⟩ := hy
    rw [hheight ((P.model q).1, top + lambda * (P.model q).2) (hsource
      ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩)]
    have hm : 0 ≤ (P.model q).2 := by
      change 0 ≤ P.vertical _ * (heightCoordinates (q : E3)).2
      exact mul_nonneg (P.vertical_pos _).le hq
    exact le_add_of_nonneg_right (mul_nonneg hlambda.le hm)
  have hequator (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 = 0) :
      P.model q = ((heightCoordinates (q : E3)).1, 0) ∧
      ‖(heightCoordinates (q : E3)).1‖ = 1 := by
    have ha : P.horizontal 0 = 1 := by simpa using P.horizontal_near 0 (by norm_num)
    refine ⟨?_, ?_⟩
    · change flatCapDiffeomorph _ _ _ _ _ _ (heightCoordinates (q : E3)) = _
      rw [flatCapDiffeomorph_apply, hq, ha, one_smul, mul_zero]
    · have hh := heightCoordinates_norm_sq (q : E3)
      rw [norm_eq_of_mem_sphere q, hq] at hh
      nlinarith [norm_nonneg (heightCoordinates (q : E3)).1]
  have hNlevel : north ∩ {y : E3 | H y = top} = rim := by
    ext y
    constructor
    · rintro ⟨⟨q, _, rfl⟩, hqH⟩
      change H (T ((P.model q).1, top + lambda * (P.model q).2)) = top at hqH
      rw [hheight ((P.model q).1, top + lambda * (P.model q).2) (hsource
        ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩)] at hqH
      have hm : (P.model q).2 = 0 :=
        (mul_eq_zero.mp (show lambda * (P.model q).2 = 0 by
          linarith only [hqH])).resolve_left hlambda.ne'
      have hqz : (heightCoordinates (q : E3)).2 = 0 := by
        change P.vertical _ * (heightCoordinates (q : E3)).2 = 0 at hm
        exact (mul_eq_zero.mp hm).resolve_left (P.vertical_pos _).ne'
      obtain ⟨hqm, hqn⟩ := hequator q hqz
      refine ⟨((heightCoordinates (q : E3)).1, top),
        ⟨mem_sphere_zero_iff_norm.mpr hqn, rfl⟩, ?_⟩
      change T ((heightCoordinates (q : E3)).1, top) =
        T ((P.model q).1, top + lambda * (P.model q).2)
      rw [hqm]
      simp only [mul_zero, add_zero]
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
      have hs' : s = top := hs
      subst s
      have hx' : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hqn : ‖heightCoordinates.symm (x, (0 : ℝ))‖ = 1 := by
        have hh := heightCoordinates_symm_norm_sq (x, (0 : ℝ))
        rw [hx'] at hh
        nlinarith [norm_nonneg (heightCoordinates.symm (x, (0 : ℝ)))]
      let q : UnitTwoSphere := ⟨heightCoordinates.symm (x, 0), mem_sphere_zero_iff_norm.mpr hqn⟩
      have hqh : (heightCoordinates (q : E3)).2 = 0 := by
        change (heightCoordinates (heightCoordinates.symm (x, 0))).2 = 0
        rw [heightCoordinates.apply_symm_apply]
      have hqm : P.model q = (x, 0) := by
        simpa only [q, heightCoordinates.apply_symm_apply] using (hequator q hqh).1
      refine ⟨⟨q, hqh.ge, ?_⟩,
        hheight _ (hsource ⟨sphere_subset_closedBall hx, mem_univ _⟩)⟩
      change T ((P.model q).1, top + lambda * (P.model q).2) = T (x, top)
      rw [hqm]
      simp only [mul_zero, add_zero]
  have hRimN : rim ⊆ north := fun _ hy => (hNlevel.symm ▸ hy).1
  have hErim : E ∩ north = rim := by
    ext y
    constructor
    · intro hy
      exact hNlevel.subset ⟨hy.2, le_antisymm (hEh y hy.1) (hNh y hy.2)⟩
    · intro hy
      exact ⟨(hElevel.symm ▸ hy).1, hRimN hy⟩
  have hdis : Disjoint A.inside L := by
    apply disjoint_left.mpr
    rintro y hyA ⟨q, hq, hqy⟩
    obtain ⟨p, hp, hpy⟩ := hAi hyA
    have heq := T.injOn
      (hsource ⟨ball_subset_closedBall hp.1, mem_univ _⟩)
      (hsource ⟨sphere_subset_closedBall hq.1, mem_univ _⟩) (hpy.trans hqy.symm)
    have hnorm : ‖p.1‖ = 1 := by
      rw [congrArg Prod.fst heq]
      exact mem_sphere_zero_iff_norm.mp hq.1
    exact (ne_of_lt (mem_ball_zero_iff.mp hp.1)) hnorm
  have havoid : A.closedRegion ∩ L ⊆ north := by
    rintro y ⟨hyA, hyL⟩
    have hyb : y ∈ A.boundary := by
      rw [← A.inside_union_boundary] at hyA
      exact hyA.resolve_left (fun h => disjoint_left.mp hdis h hyL)
    rw [hAb] at hyb
    rcases hyb with hyE | hyN
    · have hlow : top ≤ H y := by
        obtain ⟨p, hp, rfl⟩ := hyL
        rw [hheight p (hsource ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)]
        exact hp.2.1
      exact hRimN (hElevel.subset ⟨hyE, le_antisymm (hEh y hyE) hlow⟩)
    · exact hyN
  exact ⟨Q, A, ov, hov, hov1, hchart, hs, ht, hp, hi, hAb, hAi, hAc,
    hcuts, hpatch, hErim, hdis, havoid⟩

end PoincareConjecture.M25.Topology3D
