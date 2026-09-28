import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceOuterProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerGeometry









set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower



theorem reference_lower_end_geometry
    (rho : ℝ × ℝ → ℝ)
    (F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (d : ℝ)
    (T : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) (E2 × ℝ) E3 ∞)
    (hT : ∀ p : E2 × ℝ,
      T p = heightCoordinates.symm (F (p.2 - d) p.1, p.2))
    (hroot : ∀ theta ∈ Ioo (-3 / 2 : ℝ) (3 / 2),
      ∀ h ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
        Real.sqrt 15 / 4 < rho (theta, h) ∧
        rho (theta, h) < Real.sqrt 4095 / 64 ∧
        rho (theta, h) ^ 2 + Real.sqrt (1 - rho (theta, h) ^ 2) +
          rho (theta, h) * theta / 32 = h)
    (himages : ∀ h ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
      F h '' ball (0 : E2) 1 = {x : E2 | ‖x‖ < rho (x 0 / ‖x‖, h)} ∧
      F h '' closedBall (0 : E2) 1 = {x : E2 | ‖x‖ ≤ rho (x 0 / ‖x‖, h)} ∧
      F h '' sphere (0 : E2) 1 = {x : E2 | ‖x‖ = rho (x 0 / ‖x‖, h)}) :
    let C := heightCoordinates
    let U : E2 → ℝ := fun x =>
      ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
    let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
    let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
    let S : Set E3 := range j
    let Ei : ℝ → Set E3 := fun h =>
      (fun x : E2 => C.symm (x, U x + d)) '' {x | ‖x‖ < 1 / 2 ∧ U x ≤ h}
    let Eo : ℝ → Set E3 := fun h =>
      j '' {q : UnitTwoSphere | (C (q : E3)).2 ≤ 0 ∨
        rho ((C (q : E3)).1 0 / ‖(C (q : E3)).1‖, h) ≤ ‖(C (q : E3)).1‖}
    let O : Set E3 := j '' {q : UnitTwoSphere |
      (C (q : E3)).2 ≤ 0 ∨ 1 / 2 ≤ ‖(C (q : E3)).1‖}
    (∀ h ∈ J,
      IsCompact (Ei h) ∧ IsCompact (Eo h) ∧ Eo h ⊆ O ∧
      S ∩ {y : E3 | (C y).2 ≤ h + d} = Ei h ∪ Eo h ∧
      S ∩ {y : E3 | (C y).2 = h + d} =
        C.symm '' ({x : E2 | ‖x‖ < 1 / 2 ∧ U x = h} ×ˢ ({h + d} : Set ℝ)) ∪
          T '' (sphere (0 : E2) 1 ×ˢ ({h + d} : Set ℝ)) ∧
      C.symm '' ({x : E2 | ‖x‖ < 1 / 2 ∧ U x ≤ h} ×ˢ ({h + d} : Set ℝ)) ⊆
        T '' (ball (0 : E2) 1 ×ˢ ({h + d} : Set ℝ))) ∧
    ∀ a b : ℝ, a ∈ J → b ∈ J → a ≤ b →
      Eo b = Eo a ∪ T '' (sphere (0 : E2) 1 ×ˢ Icc (a + d) (b + d)) ∧
      Eo a ∩ T '' (sphere (0 : E2) 1 ×ˢ Icc (a + d) (b + d)) =
        T '' (sphere (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) := by
  classical
  dsimp only
  let C := heightCoordinates
  let U : E2 → ℝ := fun x =>
    ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
  let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
  let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
  let S : Set E3 := range j
  let Ei : ℝ → Set E3 := fun h =>
    (fun x : E2 => C.symm (x, U x + d)) '' {x | ‖x‖ < 1 / 2 ∧ U x ≤ h}
  let Eo : ℝ → Set E3 := fun h => j '' {q : UnitTwoSphere |
    (C (q : E3)).2 ≤ 0 ∨ rho ((C (q : E3)).1 0 / ‖(C (q : E3)).1‖, h) ≤
      ‖(C (q : E3)).1‖}
  let O : Set E3 := j '' {q : UnitTwoSphere |
    (C (q : E3)).2 ≤ 0 ∨ 1 / 2 ≤ ‖(C (q : E3)).1‖}
  change (∀ h ∈ J, IsCompact (Ei h) ∧ IsCompact (Eo h) ∧ Eo h ⊆ O ∧ _) ∧ _
  let theta : E2 → ℝ := fun x => x 0 / ‖x‖
  let R : ℝ → ℝ → ℝ := fun t r =>
    r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
  obtain ⟨hr0, _, hr1, _, _, hEst⟩ := radial_estimates
  have hnorm (x : E2) : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hangle (x : E2) : theta x ∈ Ioo (-3 / 2 : ℝ) (3 / 2) ∧
      ‖x‖ * theta x = x 0 := by
    have hc : -‖x‖ ≤ x 0 ∧ x 0 ≤ ‖x‖ := by
      constructor <;> nlinarith only [hnorm x, norm_nonneg x, sq_nonneg (x 1)]
    by_cases hz : ‖x‖ = 0
    · have hx := norm_eq_zero.mp hz
      subst x
      norm_num [theta]
    · have hp := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hz)
      have ht : -1 ≤ theta x ∧ theta x ≤ 1 := by
        constructor
        · exact (le_div_iff₀ hp).mpr (by simpa using hc.1)
        · exact (div_le_iff₀ hp).mpr (by simpa using hc.2)
      exact ⟨⟨by linarith only [ht.1], by linarith only [ht.2]⟩,
        mul_div_cancel₀ _ hz⟩
  have hR (x : E2) : R (theta x) ‖x‖ = U x := by
    dsimp only [R, U]
    rw [(hangle x).2]
  have hRoots (x : E2) (a : ℝ) (ha : a ∈ J) := hroot (theta x) (hangle x).1 a ha
  have hAnti (x : E2) : StrictAntiOn (R (theta x)) (Icc (Real.sqrt 15 / 4) 1) :=
    (hEst (theta x) (hangle x).1).2.2.2.2.2.2.1
  have hRootMem (x : E2) (a : ℝ) (ha : a ∈ J) :
      rho (theta x, a) ∈ Icc (Real.sqrt 15 / 4) 1 :=
    ⟨(hRoots x a ha).1.le, ((hRoots x a ha).2.1.trans hr1).le⟩
  have hRootEq (x : E2) (a : ℝ) (ha : a ∈ J) :
      R (theta x) (rho (theta x, a)) = a := (hRoots x a ha).2.2
  have hOuter (x : E2) (a : ℝ) (ha : a ∈ J)
      (hx : ‖x‖ ∈ Icc (Real.sqrt 15 / 4) 1) :
      (a ≤ U x ↔ ‖x‖ ≤ rho (theta x, a)) ∧
      (U x ≤ a ↔ rho (theta x, a) ≤ ‖x‖) := by
    simpa only [hR, hRootEq x a ha] using
      And.intro ((hAnti x).le_iff_ge (hRootMem x a ha) hx)
        ((hAnti x).le_iff_ge hx (hRootMem x a ha))
  have hMid (x : E2) (a : ℝ) (ha : a ∈ J)
      (hx : ‖x‖ ∈ Icc (1 / 2 : ℝ) (Real.sqrt 15 / 4)) : a < U x := by
    have hhigh := ha.2
    by_cases hsmall : ‖x‖ ≤ 3 / 4
    · have hmono := (hEst (theta x) (hangle x).1).2.2.2.1.monotoneOn
      have hm := hmono (show (1 / 2 : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4) by norm_num)
        (show ‖x‖ ∈ Icc (1 / 4 : ℝ) (3 / 4) from
          ⟨by linarith only [hx.1], hsmall⟩) hx.1
      have hb := (hEst (theta x) (hangle x).1).2.1
      change _ ≤ R (theta x) ‖x‖ at hm
      rw [hR] at hm
      linarith only [hm, hb, hhigh]
    · have hb := (hEst (theta x) (hangle x).1).2.2.2.2.1 ‖x‖
        ⟨(lt_of_not_ge hsmall).le, hx.2⟩
      change 73 / 64 < R (theta x) ‖x‖ at hb
      rw [hR] at hb
      linarith only [hb, hhigh]
  have hSign (x : E2) (a : ℝ) (ha : a ∈ J)
      (hx : ‖x‖ ∈ Icc (1 / 2 : ℝ) 1) :
      (U x ≤ a ↔ rho (theta x, a) ≤ ‖x‖) ∧
      (U x = a ↔ ‖x‖ = rho (theta x, a)) := by
    by_cases hlo : ‖x‖ < Real.sqrt 15 / 4
    · have hu := hMid x a ha ⟨hx.1, hlo.le⟩
      have hrootlo := (hRoots x a ha).1
      constructor <;> constructor <;> intro hh <;> linarith only [hh, hu, hlo, hrootlo]
    · have hr : ‖x‖ ∈ Icc (Real.sqrt 15 / 4) 1 := ⟨le_of_not_gt hlo, hx.2⟩
      refine ⟨(hOuter x a ha hr).2, ?_⟩
      constructor
      · intro he
        exact le_antisymm ((hOuter x a ha hr).1.mp he.ge)
          ((hOuter x a ha hr).2.mp he.le)
      · intro he
        calc
          U x = R (theta x) ‖x‖ := (hR x).symm
          _ = R (theta x) (rho (theta x, a)) := congrArg (R (theta x)) he
          _ = a := hRootEq x a ha
  have hShear (y : E3) : C (nestedReferenceDiffeomorph d y) =
      ((C y).1, (C y).2 + ‖(C y).1‖ ^ 2 + (C y).1 0 / 32 + d) := by
    rw [(nestedReferenceDiffeomorph_apply_symm d).1 y]
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · change y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d = _
      rw [hnorm]
      change y 2 + (y 0) ^ 2 + (y 1) ^ 2 + y 0 / 32 + d =
        y 2 + ((y 0) ^ 2 + (y 1) ^ 2) + y 0 / 32 + d
      ring
  have hSphere (q : UnitTwoSphere) : ‖(C (q : E3)).1‖ ≤ 1 ∧
      ((C (q : E3)).2) ^ 2 = 1 - ‖(C (q : E3)).1‖ ^ 2 := by
    have hq := heightCoordinates_norm_sq (q : E3)
    rw [norm_eq_of_mem_sphere q] at hq
    constructor <;> nlinarith only [hq, norm_nonneg (C (q : E3)).1,
      sq_nonneg (C (q : E3)).2]
  have hUpper (q : UnitTwoSphere) (hq : 0 ≤ (C (q : E3)).2) :
      j q = C.symm ((C (q : E3)).1, U (C (q : E3)).1 + d) := by
    have he : (C (q : E3)).2 = Real.sqrt (1 - ‖(C (q : E3)).1‖ ^ 2) := by
      rw [← (hSphere q).2, Real.sqrt_sq hq]
    apply C.injective
    rw [C.apply_symm_apply, hShear, he]
    apply Prod.ext
    · rfl
    · dsimp only [U]
      ring
  have hLower (q : UnitTwoSphere) (hq : (C (q : E3)).2 ≤ 0)
      (a : ℝ) (ha : a ∈ J) : (C (j q)).2 < a + d := by
    have hn := (hSphere q).1
    have habs : |(C (q : E3)).1 0| ≤ ‖(C (q : E3)).1‖ :=
      PiLp.norm_apply_le (C (q : E3)).1 0
    have hc := (le_abs_self ((C (q : E3)).1 0)).trans habs
    have hh := ha.1
    rw [hShear]
    dsimp only
    nlinarith only [hn, hc, hq, hh, norm_nonneg (C (q : E3)).1]
  have hLift (x : E2) (hx : ‖x‖ ≤ 1) : ∃ q : UnitTwoSphere,
      C (q : E3) = (x, Real.sqrt (1 - ‖x‖ ^ 2)) ∧
      j q = C.symm (x, U x + d) := by
    let y := C.symm (x, Real.sqrt (1 - ‖x‖ ^ 2))
    have hs : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith only [hx, norm_nonneg x]
    have hy : ‖y‖ = 1 := by
      have hn : ‖y‖ ^ 2 = 1 := by
        rw [heightCoordinates_symm_norm_sq, Real.sq_sqrt hs]
        ring
      nlinarith only [hn, norm_nonneg y]
    let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
    have hq : C (q : E3) = (x, Real.sqrt (1 - ‖x‖ ^ 2)) := C.apply_symm_apply _
    refine ⟨q, hq, ?_⟩
    rw [hUpper q (by rw [hq]; exact Real.sqrt_nonneg _), hq]
  have hjinj : Function.Injective j := fun q r hqr =>
    Subtype.ext ((nestedReferenceDiffeomorph d).injective hqr)
  have hO (q : UnitTwoSphere) : j q ∈ O ↔
      (C (q : E3)).2 ≤ 0 ∨ 1 / 2 ≤ ‖(C (q : E3)).1‖ := by
    constructor
    · rintro ⟨r, hr, he⟩
      exact hjinj he ▸ hr
    · intro hq
      exact ⟨q, hq, rfl⟩
  have hEo (a : ℝ) (ha : a ∈ J) (y : E3) :
      y ∈ Eo a ↔ y ∈ S ∧ y ∈ O ∧ (C y).2 ≤ a + d := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q, rfl⟩, ?_, ?_⟩
      · apply (hO q).mpr
        rcases hq with hq | hq
        · exact Or.inl hq
        · right
          have hh := (hRoots (C (q : E3)).1 a ha).1
          linarith only [hr0, hh, hq]
      · by_cases hlow : (C (q : E3)).2 ≤ 0
        · exact (hLower q hlow a ha).le
        · have hrad := hq.resolve_left hlow
          have hu := (hOuter (C (q : E3)).1 a ha
            ⟨(hRoots _ a ha).1.le.trans hrad, (hSphere q).1⟩).2.mpr hrad
          rw [hUpper q (le_of_not_ge hlow), C.apply_symm_apply]
          dsimp only
          linarith only [hu]
    · rintro ⟨⟨q, rfl⟩, hqO, hheight⟩
      refine ⟨q, ?_, rfl⟩
      by_cases hlow : (C (q : E3)).2 ≤ 0
      · exact Or.inl hlow
      · right
        have hrad := ((hO q).mp hqO).resolve_left hlow
        rw [hUpper q (le_of_not_ge hlow), C.apply_symm_apply] at hheight
        exact (hSign _ a ha ⟨hrad, (hSphere q).1⟩).1.mp
          (le_of_add_le_add_right hheight)
  have hTflat (a : ℝ) (x : E2) : T (x, a + d) = C.symm (F a x, a + d) := by
    rw [hT, add_sub_cancel_right]
  have hTheight (p : E2 × ℝ) : (C (T p)).2 = p.2 := by
    rw [hT, C.apply_symm_apply]
  have hCircle (a : ℝ) (ha : a ∈ J) (y : E3) :
      y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ↔
      ∃ x : E2, ‖x‖ = rho (theta x, a) ∧ C.symm (x, a + d) = y := by
    constructor
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
      have hs' : s = a + d := hs
      subst s
      have hf : F a x ∈ F a '' sphere (0 : E2) 1 := ⟨x, hx, rfl⟩
      rw [(himages a ha).2.2] at hf
      exact ⟨F a x, hf, (hTflat a x).symm⟩
    · rintro ⟨x, hx, he⟩
      have hf : x ∈ F a '' sphere (0 : E2) 1 := by
        rw [(himages a ha).2.2]
        exact hx
      obtain ⟨v, hv, hvx⟩ := hf
      refine ⟨(v, a + d), ⟨hv, rfl⟩, ?_⟩
      rw [hTflat, hvx]
      exact he
  have hCircleSet (a : ℝ) (ha : a ∈ J) (y : E3) :
      y ∈ T '' (sphere (0 : E2) 1 ×ˢ ({a + d} : Set ℝ)) ↔
      y ∈ S ∧ y ∈ O ∧ (C y).2 = a + d := by
    rw [hCircle a ha y]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hn : ‖x‖ < 1 := hx ▸ (hRoots x a ha).2.1.trans hr1
      have hu : U x = a := by
        calc
          U x = R (theta x) ‖x‖ := (hR x).symm
          _ = R (theta x) (rho (theta x, a)) := congrArg (R (theta x)) hx
          _ = a := hRootEq x a ha
      obtain ⟨q, hq, hjq⟩ := hLift x hn.le
      rw [hu] at hjq
      refine ⟨⟨q, hjq⟩, ?_, ?_⟩
      · rw [← hjq, hO, hq]
        right
        have hh := (hRoots x a ha).1
        dsimp only
        linarith only [hx, hh, hr0]
      · exact congrArg Prod.snd (C.apply_symm_apply (x, a + d))
    · rintro ⟨⟨q, rfl⟩, hqO, hheight⟩
      have hpos : 0 < (C (q : E3)).2 := by
        by_contra hn
        have hh := hLower q (le_of_not_gt hn) a ha
        exact (ne_of_lt hh) hheight
      have hrad := ((hO q).mp hqO).resolve_left (not_le_of_gt hpos)
      have he := hUpper q hpos.le
      have hu : U (C (q : E3)).1 = a := by
        rw [he, C.apply_symm_apply] at hheight
        exact add_right_cancel hheight
      exact ⟨(C (q : E3)).1, (hSign _ a ha ⟨hrad, (hSphere q).1⟩).2.mp hu,
        by rw [← hu]; exact he.symm⟩
  have hUcont : Continuous U :=
    ((continuous_norm.pow 2).add
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))).add
      ((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.div_const 32)
  have hjcont : Continuous j :=
    (nestedReferenceDiffeomorph d).continuous.comp continuous_subtype_val
  have hCcont : Continuous (fun q : UnitTwoSphere => C (q : E3)) :=
    C.continuous.comp continuous_subtype_val
  have hCompactInner (a : ℝ) (ha : a ∈ J) : IsCompact (Ei a) := by
    obtain ⟨_, _, _, _, _, _, vmin, _, _, _, _, _, _, _, hsub⟩ :=
      inner_reference_convex_geometry
    obtain ⟨hc, hs⟩ := hsub a (by linarith only [ha.2])
    have he : {x : E2 | x ∈ closedBall 0 (1 / 2) ∧ U x ≤ a} =
        {x : E2 | ‖x‖ < 1 / 2 ∧ U x ≤ a} := by
      ext x
      constructor
      · intro hx
        exact ⟨mem_ball_zero_iff.mp (hs hx), hx.2⟩
      · rintro ⟨hx, hu⟩
        exact ⟨mem_closedBall_zero_iff.mpr hx.le, hu⟩
    change IsCompact ((fun x : E2 => C.symm (x, U x + d)) '' _)
    have hc' : IsCompact {x : E2 | ‖x‖ < 1 / 2 ∧ U x ≤ a} := by
      rw [← he]
      exact hc
    apply hc'.image
    exact C.symm.continuous.comp (continuous_id.prodMk (hUcont.add continuous_const))
  have hCompactOuter (a : ℝ) (ha : a ∈ J) : IsCompact (Eo a) := by
    have he : {q : UnitTwoSphere | (C (q : E3)).2 ≤ 0 ∨
        rho (theta (C (q : E3)).1, a) ≤ ‖(C (q : E3)).1‖} =
        {q : UnitTwoSphere | (C (q : E3)).2 ≤ 0 ∨
          1 / 2 ≤ ‖(C (q : E3)).1‖ ∧ U (C (q : E3)).1 ≤ a} := by
      ext q
      constructor
      · rintro (hq | hq)
        · exact Or.inl hq
        · have hr : 1 / 2 ≤ ‖(C (q : E3)).1‖ := by
            have hh := (hRoots (C (q : E3)).1 a ha).1
            linarith only [hh, hq, hr0]
          exact Or.inr ⟨hr, (hSign _ a ha ⟨hr, (hSphere q).1⟩).1.mpr hq⟩
      · rintro (hq | ⟨hr, hu⟩)
        · exact Or.inl hq
        · exact Or.inr ((hSign _ a ha ⟨hr, (hSphere q).1⟩).1.mp hu)
    have hc : IsClosed {q : UnitTwoSphere | (C (q : E3)).2 ≤ 0 ∨
        1 / 2 ≤ ‖(C (q : E3)).1‖ ∧ U (C (q : E3)).1 ≤ a} :=
      (isClosed_le hCcont.snd continuous_const).union
        ((isClosed_le continuous_const hCcont.fst.norm).inter
          (isClosed_le (hUcont.comp hCcont.fst) continuous_const))
    change IsCompact (j '' _)
    rw [he]
    exact hc.isCompact.image hjcont
  constructor
  · intro a ha
    refine ⟨hCompactInner a ha, hCompactOuter a ha,
      fun y hy => ((hEo a ha y).mp hy).2.1, ?_, ?_, ?_⟩
    · apply Subset.antisymm
      · rintro y ⟨⟨q, rfl⟩, hh⟩
        by_cases hlow : (C (q : E3)).2 ≤ 0
        · exact Or.inr ⟨q, Or.inl hlow, rfl⟩
        · by_cases hr : ‖(C (q : E3)).1‖ < 1 / 2
          · left
            have he := hUpper q (le_of_not_ge hlow)
            refine ⟨(C (q : E3)).1, ⟨hr, ?_⟩, he.symm⟩
            change (C (j q)).2 ≤ a + d at hh
            rw [he, C.apply_symm_apply] at hh
            exact le_of_add_le_add_right hh
          · right
            exact (hEo a ha (j q)).mpr
              ⟨⟨q, rfl⟩, (hO q).mpr (Or.inr (le_of_not_gt hr)), hh⟩
      · intro y hy
        rcases hy with ⟨x, ⟨hx, hu⟩, rfl⟩ | hy
        · obtain ⟨q, _hq, he⟩ := hLift x (by linarith only [hx])
          refine ⟨⟨q, he⟩, ?_⟩
          change (C (C.symm (x, U x + d))).2 ≤ a + d
          rw [C.apply_symm_apply]
          change U x ≤ a at hu
          dsimp only
          linarith only [hu]
        · have hh := (hEo a ha y).mp hy
          exact ⟨hh.1, hh.2.2⟩
    · apply Subset.antisymm
      · rintro y ⟨⟨q, rfl⟩, hh⟩
        have hpos : 0 < (C (q : E3)).2 := by
          by_contra hn
          exact (ne_of_lt (hLower q (le_of_not_gt hn) a ha)) hh
        by_cases hr : ‖(C (q : E3)).1‖ < 1 / 2
        · have he := hUpper q hpos.le
          have hu : U (C (q : E3)).1 = a := by
            change (C (j q)).2 = a + d at hh
            rw [he, C.apply_symm_apply] at hh
            exact add_right_cancel hh
          left
          refine ⟨((C (q : E3)).1, a + d), ⟨⟨hr, hu⟩, rfl⟩, ?_⟩
          rw [← hu]
          exact he.symm
        · exact Or.inr ((hCircleSet a ha (j q)).mpr
            ⟨⟨q, rfl⟩, (hO q).mpr (Or.inr (le_of_not_gt hr)), hh⟩)
      · intro y hy
        rcases hy with ⟨⟨x, s⟩, ⟨⟨hx, hu⟩, hs⟩, rfl⟩ | hy
        · have hs' : s = a + d := hs
          subst s
          obtain ⟨q, _hq, he⟩ := hLift x (by linarith only [hx])
          change U x = a at hu
          rw [hu] at he
          exact ⟨⟨q, he⟩, congrArg Prod.snd (C.apply_symm_apply _)⟩
        · have hh := (hCircleSet a ha y).mp hy
          exact ⟨hh.1, hh.2.2⟩
    · rintro y ⟨⟨x, s⟩, ⟨⟨hx, _hu⟩, hs⟩, rfl⟩
      have hs' : s = a + d := hs
      subst s
      have hf : x ∈ F a '' ball (0 : E2) 1 := by
        rw [(himages a ha).1]
        have hr := (hRoots x a ha).1
        change ‖x‖ < rho (theta x, a)
        linarith only [hx, hr, hr0]
      obtain ⟨v, hv, he⟩ := hf
      exact ⟨(v, a + d), ⟨hv, rfl⟩, by rw [hTflat, he]⟩
  · intro a b ha hb hab
    have hCyl (y : E3) :
        y ∈ T '' (sphere (0 : E2) 1 ×ˢ Icc (a + d) (b + d)) ↔
        y ∈ S ∧ y ∈ O ∧ a + d ≤ (C y).2 ∧ (C y).2 ≤ b + d := by
      constructor
      · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
        have hJ : s - d ∈ J := by
          constructor <;> linarith only [hs.1, hs.2, ha.1, hb.2]
        have hslice : T (x, s) ∈
            T '' (sphere (0 : E2) 1 ×ˢ ({s - d + d} : Set ℝ)) :=
          ⟨(x, s), ⟨hx, by simp⟩, rfl⟩
        have hh := (hCircleSet (s - d) hJ (T (x, s))).mp hslice
        exact ⟨hh.1, hh.2.1, by rw [hTheight]; exact hs⟩
      · rintro ⟨hyS, hyO, hlo, hhi⟩
        have hJ : (C y).2 - d ∈ J := by
          constructor <;> linarith only [hlo, hhi, ha.1, hb.2]
        have hslice := (hCircleSet ((C y).2 - d) hJ y).mpr
          ⟨hyS, hyO, by ring⟩
        obtain ⟨⟨x, s⟩, ⟨hx, hs⟩, he⟩ := hslice
        have hs' : s = (C y).2 := by simpa using hs
        refine ⟨(x, s), ⟨hx, ?_⟩, he⟩
        rw [hs']
        exact ⟨hlo, hhi⟩
    constructor
    · ext y
      rw [mem_union, hEo b hb y, hEo a ha y, hCyl y]
      constructor
      · rintro ⟨hyS, hyO, hh⟩
        rcases le_total (C y).2 (a + d) with hlo | hhi
        · exact Or.inl ⟨hyS, hyO, hlo⟩
        · exact Or.inr ⟨hyS, hyO, hhi, hh⟩
      · rintro (⟨hyS, hyO, hh⟩ | ⟨hyS, hyO, _hlo, hh⟩)
        · exact ⟨hyS, hyO, by linarith only [hh, hab]⟩
        · exact ⟨hyS, hyO, hh⟩
    · ext y
      rw [mem_inter_iff, hEo a ha y, hCyl y, hCircleSet a ha y]
      constructor
      · rintro ⟨⟨hyS, hyO, hlo⟩, _hyS, _hyO, hhi, _hb⟩
        exact ⟨hyS, hyO, le_antisymm hlo hhi⟩
      · rintro ⟨hyS, hyO, hh⟩
        refine ⟨⟨hyS, hyO, hh.le⟩, hyS, hyO, hh.ge, ?_⟩
        rw [hh]
        linarith only [hab]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
