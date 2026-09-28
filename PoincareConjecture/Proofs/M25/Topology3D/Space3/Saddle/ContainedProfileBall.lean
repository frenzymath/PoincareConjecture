import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallBoundaryContainment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlatCapBall
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic









set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_contained_profile_ball
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p ∈ T.source, ⟪(u : E3), T p⟫_ℝ = p.2)
    (A : BallNeighborhoodChart E3 E3)
    (ell top lambda tau : ℝ) (hlambda : 0 < lambda)
    (hgap : lambda * P.heightBound < top - ell)
    (hshort : lambda * P.heightBound < tau)
    (hfilled : ∀ t ∈ Icc ell top,
      T '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ A.closedRegion)
    (hnorth : (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ⊆
          A.closedRegion) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    let north := (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let south := (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    ∃ N : BallNeighborhoodChart E3 E3,
      N.boundary = south ∪ north ∧
      N.chart.source = {y : E3 | ((M (heightCoordinates y)).1,
        top + lambda * (M (heightCoordinates y)).2) ∈ T.source} ∧
      N.chart.target = T.target ∧
      (∀ y : E3, N.chart y = T ((M (heightCoordinates y)).1,
        top + lambda * (M (heightCoordinates y)).2)) ∧
      (∀ y : E3, N.chart.symm y = heightCoordinates.symm
        (M.symm ((T.symm y).1, ((T.symm y).2 - top) / lambda))) ∧
      N.closedRegion ⊆ A.closedRegion ∧
      N.closedRegion ⊆ {y : E3 | |H y - top| < tau} ∧
      north = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} ∧
      south ∩ north = T '' (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ)) := by
  classical
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  let J := heightCoordinates.toDiffeomorph.trans M
  let B : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ := {
    toEquiv := {
      toFun := fun p => (p.1, top + lambda * p.2)
      invFun := fun p => (p.1, (p.2 - top) / lambda)
      left_inv := by
        rintro ⟨x, z⟩
        apply Prod.ext
        · rfl
        change (top + lambda * z - top) / lambda = z
        field_simp [hlambda.ne']
        ring
      right_inv := by
        rintro ⟨x, z⟩
        apply Prod.ext
        · rfl
        change top + lambda * ((z - top) / lambda) = z
        field_simp [hlambda.ne']
        ring }
    contMDiff_toFun := (by
      fun_prop : ContDiff ℝ ∞ (fun p : E2 × ℝ => (p.1, top + lambda * p.2))).contMDiff
    contMDiff_invFun := (by
      fun_prop : ContDiff ℝ ∞ (fun p : E2 × ℝ => (p.1, (p.2 - top) / lambda))).contMDiff }
  let Q := J.trans B
  have hhor (y : E3) (hy : y ∈ closedBall (0 : E3) 1) : ‖(J y).1‖ ≤ 1 := by
    apply flatCapDiffeomorph_fst_norm_le P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound
    change ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 ≤ 1
    rw [← heightCoordinates_norm_sq]
    have hy' := mem_closedBall_zero_iff.mp hy
    nlinarith [norm_nonneg y]
  have hQs (y : E3) (hy : y ∈ closedBall (0 : E3) 1) : Q y ∈ T.source :=
    hsource ⟨mem_closedBall_zero_iff.mpr (hhor y hy), mem_univ _⟩
  let N : BallNeighborhoodChart E3 E3 := {
    chart := Q.toHomeomorph.toOpenPartialHomeomorph.trans T
    closedBall_subset_source := fun y hy => ⟨mem_univ y, hQs y hy⟩
    smooth := hT.comp Q.contMDiff_toFun.contDiff.contDiffOn (fun _ hp => hp.2)
    smooth_symm := Q.contMDiff_invFun.contDiff.comp_contDiffOn
      (hTi.mono (fun _ hp => hp.1)) }
  let F : UnitTwoSphere → E3 := fun q =>
    T ((P.model q).1, top + lambda * (P.model q).2)
  let north := F '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let south := F '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  have hNpoint (y : E3) : N.chart y = T ((M (heightCoordinates y)).1,
      top + lambda * (M (heightCoordinates y)).2) := rfl
  have hNF (q : UnitTwoSphere) : N.chart (q : E3) = F q := rfl
  have hNsource : N.chart.source = {y : E3 | ((M (heightCoordinates y)).1,
      top + lambda * (M (heightCoordinates y)).2) ∈ T.source} := by
    ext y
    change (y ∈ (univ : Set E3) ∧ Q y ∈ T.source) ↔ Q y ∈ T.source
    simp only [mem_univ, true_and]
  have hNtarget : N.chart.target = T.target := by
    ext y
    change (y ∈ T.target ∧ T.symm y ∈ (univ : Set (E2 × ℝ))) ↔ y ∈ T.target
    simp only [mem_univ, and_true]
  have hNinv (y : E3) : N.chart.symm y = heightCoordinates.symm
      (M.symm ((T.symm y).1, ((T.symm y).2 - top) / lambda)) := rfl
  have hboundary : N.boundary = south ∪ north := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases le_total (heightCoordinates q).2 0 with hm | hp
      · exact Or.inl ⟨⟨q, hq⟩, hm, rfl⟩
      · exact Or.inr ⟨⟨q, hq⟩, hp, rfl⟩
    · rintro (⟨q, _, rfl⟩ | ⟨q, _, rfl⟩)
      · exact ⟨(q : E3), q.property, rfl⟩
      · exact ⟨(q : E3), q.property, rfl⟩
  have hJclosed : IsCompact (J '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall (0 : E3) 1).image J.continuous
  have hJopen : IsOpen (J '' ball (0 : E3) 1) := J.toHomeomorph.isOpenMap _ isOpen_ball
  have hJne : (J '' closedBall (0 : E3) 1).Nonempty := ⟨J 0, 0, by simp, rfl⟩
  have hext (sigma : ℝ) (hsigma : |sigma| = 1) :
      ∀ p ∈ J '' closedBall (0 : E3) 1, sigma * p.2 ≤ P.heightBound := by
    obtain ⟨p, hp, hmax⟩ := hJclosed.exists_isMaxOn hJne
      (f := fun p : E2 × ℝ => sigma * p.2) (by fun_prop)
    obtain ⟨y, hy, rfl⟩ := hp
    have hyb : y ∈ sphere (0 : E3) 1 := by
      by_contra hyb
      have hyn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
      have hyl : ‖y‖ < 1 := lt_of_le_of_ne hyn
        (fun heq => hyb (mem_sphere_zero_iff_norm.mpr heq))
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hJopen (J y)
        ⟨y, mem_ball_zero_iff.mpr hyl, rfl⟩
      let p' : E2 × ℝ := ((J y).1, (J y).2 + sigma * (r / 2))
      have hp' : p' ∈ J '' closedBall (0 : E3) 1 := by
        apply image_mono ball_subset_closedBall
        apply hsub
        change dist ((J y).1, (J y).2 + sigma * (r / 2)) ((J y).1, (J y).2) < r
        rw [dist_prod_same_left, Real.dist_eq,
          show (J y).2 + sigma * (r / 2) - (J y).2 = sigma * (r / 2) by ring,
          abs_mul, hsigma, one_mul, abs_of_pos (by positivity : 0 < r / 2)]
        linarith
      have hsquare : sigma ^ 2 = 1 := by nlinarith [sq_abs sigma]
      have hstep : sigma * p'.2 = sigma * (J y).2 + r / 2 := by
        dsimp [p']
        calc
          _ = sigma * (J y).2 + sigma ^ 2 * (r / 2) := by ring
          _ = _ := by rw [hsquare, one_mul]
      have h : sigma * p'.2 ≤ sigma * (J y).2 := hmax hp'
      rw [hstep] at h
      linarith
    have hbnd : |(J y).2| ≤ P.heightBound := P.height_bound ⟨y, hyb⟩
    have hsign : sigma * (J y).2 ≤ |(J y).2| := by
      calc
        _ ≤ |sigma * (J y).2| := le_abs_self _
        _ = _ := by rw [abs_mul, hsigma, one_mul]
    exact fun p hp => (hmax hp).trans (hsign.trans hbnd)
  have hJheight (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      |(J y).2| ≤ P.heightBound := by
    have hm := hext (-1) (by norm_num) (J y) ⟨y, hy, rfl⟩
    have hp := hext 1 (by norm_num) (J y) ⟨y, hy, rfl⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hheightN : N.closedRegion ⊆ {y : E3 | |H y - top| < tau} := by
    rintro y ⟨v, hv, rfl⟩
    have hz : H (N.chart v) = top + lambda * (J v).2 := hheight (Q v) (hQs v hv)
    change |H (N.chart v) - top| < tau
    rw [hz, add_sub_cancel_left, abs_mul, abs_of_pos hlambda]
    exact (mul_le_mul_of_nonneg_left (hJheight v hv) hlambda.le).trans_lt hshort
  have hsouth : south ⊆ A.closedRegion := by
    rintro y ⟨q, hq, rfl⟩
    have hmodel : (P.model q).2 ≤ 0 := by
      change P.vertical _ * (heightCoordinates (q : E3)).2 ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (P.vertical_pos _).le hq
    have hlo : -P.heightBound ≤ (P.model q).2 := (abs_le.mp (P.height_bound q)).1
    have ht : top + lambda * (P.model q).2 ∈ Icc ell top := by
      have hl := mul_le_mul_of_nonneg_left hlo hlambda.le
      have hu := mul_nonpos_of_nonneg_of_nonpos hlambda.le hmodel
      constructor <;> linarith
    apply hfilled _ ht
    exact ⟨((P.model q).1, top + lambda * (P.model q).2),
      ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), rfl⟩, rfl⟩
  have hcontain : N.closedRegion ⊆ A.closedRegion := by
    apply saddle_ball_closedRegion_subset_of_boundary_subset A N
    rw [hboundary]
    exact union_subset hsouth hnorth
  have hnorthEq : north = N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, rfl⟩
    · rintro ⟨q, ⟨hqn, hqh⟩, rfl⟩
      exact ⟨⟨q, mem_sphere_zero_iff_norm.mpr hqn⟩, hqh, rfl⟩
  have hequator (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 = 0) :
      P.model q = ((heightCoordinates (q : E3)).1, 0) ∧
      ‖(heightCoordinates (q : E3)).1‖ = 1 := by
    have ha : P.horizontal 0 = 1 := by
      simpa using P.horizontal_near 0 (by norm_num)
    refine ⟨?_, ?_⟩
    · change M (heightCoordinates (q : E3)) = _
      rw [flatCapDiffeomorph_apply, hq, ha, one_smul, mul_zero]
    · have hh := heightCoordinates_norm_sq (q : E3)
      rw [norm_eq_of_mem_sphere q, hq] at hh
      nlinarith [norm_nonneg (heightCoordinates (q : E3)).1]
  have hmeet : south ∩ north = T ''
      (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨q, hq, hqy⟩, ⟨r, hr, hry⟩⟩
      have hqr : q = r := by
        apply Subtype.ext
        apply N.chart.injOn
          (N.closedBall_subset_source (sphere_subset_closedBall q.property))
          (N.closedBall_subset_source (sphere_subset_closedBall r.property))
        exact hqy.trans hry.symm
      subst r
      obtain ⟨hm, hn⟩ := hequator q (le_antisymm hq hr)
      refine ⟨((heightCoordinates (q : E3)).1, top),
        ⟨mem_sphere_zero_iff_norm.mpr hn, rfl⟩, ?_⟩
      have hh : F q = T ((heightCoordinates (q : E3)).1, top) := by
        dsimp [F]
        rw [hm]
        simp only [mul_zero, add_zero]
      exact hh.symm.trans hqy
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = top := ht
      subst t
      have hx' : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hqn : ‖heightCoordinates.symm (x, (0 : ℝ))‖ = 1 := by
        have hh := heightCoordinates_symm_norm_sq (x, (0 : ℝ))
        rw [hx'] at hh
        nlinarith [norm_nonneg (heightCoordinates.symm (x, (0 : ℝ)))]
      let q : UnitTwoSphere := ⟨heightCoordinates.symm (x, 0),
        mem_sphere_zero_iff_norm.mpr hqn⟩
      have hqh : (heightCoordinates (q : E3)).2 = 0 := by
        change (heightCoordinates (heightCoordinates.symm (x, (0 : ℝ)))).2 = 0
        rw [heightCoordinates.apply_symm_apply]
      have hqm : P.model q = (x, 0) := by
        simpa only [q, heightCoordinates.apply_symm_apply] using (hequator q hqh).1
      have hFq : F q = T (x, top) := by
        dsimp [F]
        rw [hqm]
        simp only [mul_zero, add_zero]
      exact ⟨⟨q, hqh.le, hFq⟩, ⟨q, hqh.ge, hFq⟩⟩
  exact ⟨N, hboundary, hNsource, hNtarget, hNpoint, hNinv,
    hcontain, hheightN, hnorthEq, hmeet⟩

end PoincareConjecture.M25.Topology3D
