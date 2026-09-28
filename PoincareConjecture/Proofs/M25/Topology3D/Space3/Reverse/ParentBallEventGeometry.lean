import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEventRegions
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryDiscIntersection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapEmbedding
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


noncomputable def RegularSurgeryEvent.reunionTube
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2) :
    OpenPartialHomeomorph (E2 × ℝ) E3 :=
  (surgeryCapPlacementDiffeomorph E.cutHeight (![1, -1] i) 0 1
    (by fin_cases i <;> norm_num) (by norm_num)).toHomeomorph.toOpenPartialHomeomorph.trans
      E.data.tube


theorem RegularSurgeryEvent.reunionTube_spec
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2) :
    let sigma : ℝ := ![1, -1] i
    let T := E.reunionTube i
    (∀ p : E2 × ℝ, T p = E.data.tube (p.1, E.cutHeight + sigma * p.2)) ∧
      T.source = {p : E2 × ℝ |
        (p.1, E.cutHeight + sigma * p.2) ∈ E.data.tube.source} ∧
      T.target = E.data.tube.target ∧
      (∀ y : E3, T.symm y =
        ((E.data.tube.symm y).1,
          ((E.data.tube.symm y).2 - E.cutHeight) / sigma)) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
      ContDiffOn ℝ ∞ T T.source ∧
      ContDiffOn ℝ ∞ T.symm T.target ∧
      ∀ p : E2 × ℝ, ⟪(u : E3), T p⟫_ℝ = E.cutHeight + sigma * p.2 := by
  let sigma : ℝ := ![1, -1] i
  let T := E.reunionTube i
  have hsigma : sigma ≠ 0 := by fin_cases i <;> norm_num [sigma]
  let D := surgeryCapPlacementDiffeomorph E.cutHeight sigma 0 1 hsigma one_ne_zero
  have happ (p : E2 × ℝ) : T p = E.data.tube (p.1, E.cutHeight + sigma * p.2) := by
    change E.data.tube (p.1, E.cutHeight + sigma * (0 + 1 * p.2)) = _
    simp only [zero_add, one_mul]
  refine ⟨happ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    change (p ∈ (univ : Set (E2 × ℝ)) ∧
      (p.1, E.cutHeight + sigma * (0 + 1 * p.2)) ∈ E.data.tube.source) ↔
        (p.1, E.cutHeight + sigma * p.2) ∈ E.data.tube.source
    simp only [mem_univ, true_and, zero_add, one_mul]
  · ext y
    change (y ∈ E.data.tube.target ∧
      E.data.tube.symm y ∈ (univ : Set (E2 × ℝ))) ↔ y ∈ E.data.tube.target
    simp only [mem_univ, and_true]
  · intro y
    change ((E.data.tube.symm y).1,
      (1 : ℝ)⁻¹ * (sigma⁻¹ * ((E.data.tube.symm y).2 - E.cutHeight) - 0)) = _
    simp only [inv_one, one_mul, sub_zero]
    apply Prod.ext
    · rfl
    · change sigma⁻¹ * ((E.data.tube.symm y).2 - E.cutHeight) =
        ((E.data.tube.symm y).2 - E.cutHeight) / sigma
      rw [div_eq_mul_inv, mul_comm]
  · intro p hp
    change p ∈ (univ : Set (E2 × ℝ)) ∧
      (p.1, E.cutHeight + sigma * (0 + 1 * p.2)) ∈ E.data.tube.source
    exact ⟨mem_univ _, E.data.tube_source ⟨hp.1, mem_univ _⟩⟩
  · exact E.data.tube_smooth.comp D.contMDiff_toFun.contDiff.contDiffOn
      (fun _ hp => hp.2)
  · exact D.contMDiff_invFun.contDiff.comp_contDiffOn
      (E.data.tube_inverse.mono (fun _ hy => hy.1))
  · intro p
    rw [happ, E.data.tube_height]


theorem RegularSurgeryEvent.reunion_core_isCompact
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2) :
    IsCompact ((fun p : UnitTwoSphere => parent (p, 0)) ''
      ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
        closedBall (0 : E2) E.radius)) := by
  let e := (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i)
  have he : closedBall (0 : E2) 1 ⊆ e.source := by
    fin_cases i
    · exact E.data.sourceDiscs.positive_source
    · exact E.data.sourceDiscs.negative_source
  have her : closedBall (0 : E2) E.radius ⊆ e.source :=
    (closedBall_subset_closedBall E.radius_mem.2.le).trans he
  exact ((isCompact_closedBall (0 : E2) E.radius).image_of_continuousOn
    (e.continuousOn.mono her)).image
      (collar_central_contMDiff parent E.parent_embedding).continuous


theorem RegularSurgeryEvent.reunion_core_disjoint_strip
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2) :
    let a := E.data.width / 2 * (1 - E.radius)
    let core := (fun p : UnitTwoSphere => parent (p, 0)) ''
      ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
        closedBall (0 : E2) E.radius)
    Disjoint core ((E.reunionTube i) ''
      (closedBall (0 : E2) 1 ×ˢ Ioo (-E.data.width) a)) := by
  let a := E.data.width / 2 * (1 - E.radius)
  let e := (![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i)
  let sigma : ℝ := ![1, -1] i
  obtain ⟨_hdelta, _ha, hak, hkd, _hl, _hsmall⟩ := E.parameter_bounds
  have had : a < E.data.width := hak.trans hkd
  have hk : 0 < E.data.width / 2 := div_pos E.data.width_pos (by norm_num)
  have he : closedBall (0 : E2) 1 ⊆ e.source := by
    fin_cases i
    · exact E.data.sourceDiscs.positive_source
    · exact E.data.sourceDiscs.negative_source
  have hsmall : closedBall (0 : E2) E.radius ⊆ ball 0 1 := fun x hx =>
    mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt E.radius_mem.2)
  have hcentral : Function.Injective (fun p : UnitTwoSphere => parent (p, 0)) := by
    intro p q hpq
    exact congrArg Prod.fst (E.parent_embedding.2.1 (by simp) (by simp) hpq)
  change Disjoint ((fun p : UnitTwoSphere => parent (p, 0)) ''
    (e '' closedBall (0 : E2) E.radius))
      ((E.reunionTube i) '' (closedBall (0 : E2) 1 ×ˢ Ioo (-E.data.width) a))
  apply disjoint_left.mpr
  rintro y ⟨q, hq, hqy⟩ ⟨p, hp, hpy⟩
  obtain ⟨x, hx, rfl⟩ := hq
  have hpoint : parent (e x, 0) =
      E.data.tube (p.1, E.cutHeight + sigma * p.2) :=
    hqy.trans (hpy.symm.trans ((E.reunionTube_spec i).1 p))
  have hband : sigma * p.2 ∈ Ioo (-E.data.width) E.data.width := by
    fin_cases i
    · simpa [sigma] using
        (show p.2 ∈ Ioo (-E.data.width) E.data.width from ⟨hp.2.1, hp.2.2.trans had⟩)
    · have hneg : -p.2 ∈ Ioo (-E.data.width) E.data.width :=
        ⟨by linarith only [hp.2.2, had], by linarith only [hp.2.1]⟩
      simpa [sigma] using hneg
  have hphysical : E.cutHeight + sigma * p.2 ∈
      Ioo (E.cutHeight - E.data.width) (E.cutHeight + E.data.width) :=
    ⟨by linarith only [hband.1], by linarith only [hband.2]⟩
  have hcircle : p.1 ∈ sphere (0 : E2) 1 :=
    (E.data.surface_mem p.1 hp.1 _ hphysical).mp ⟨e x, hpoint⟩
  let theta : UnitCircle := ⟨p.1, hcircle⟩
  have hrec := E.data.reconstruction theta (sigma * p.2) hband
  have hretained : E.data.sourceCollar (theta, sigma * p.2) ∈
      e '' closedBall (0 : E2) E.radius := by
    rw [hcentral (hrec.trans hpoint.symm)]
    exact ⟨x, hx, rfl⟩
  by_cases hneg : p.2 < 0
  · fin_cases i
    · have hchosen : E.data.sourceCollar (theta, p.2) ∈
          E.data.sourceDiscs.positive '' ball (0 : E2) 1 := by
        simpa [e, sigma] using image_mono hsmall hretained
      have hopposite := E.data.sourceDiscs.negative_side
        (show E.data.sourceCollar (theta, p.2) ∈ E.data.sourceCollar ''
          (univ ×ˢ Ioo (-E.data.width) 0) from
            ⟨(theta, p.2), ⟨mem_univ _, hp.2.1, hneg⟩, rfl⟩)
      exact disjoint_left.mp E.data.sourceDiscs.open_disjoint hchosen hopposite
    · have hchosen : E.data.sourceCollar (theta, -p.2) ∈
          E.data.sourceDiscs.negative '' ball (0 : E2) 1 := by
        simpa [e, sigma] using image_mono hsmall hretained
      have hopposite := E.data.sourceDiscs.positive_side
        (show E.data.sourceCollar (theta, -p.2) ∈ E.data.sourceCollar ''
          (univ ×ˢ Ioo 0 E.data.width) from
            ⟨(theta, -p.2), ⟨mem_univ _, by linarith only [hneg],
              by linarith only [hp.2.1]⟩, rfl⟩)
      exact disjoint_left.mp E.data.sourceDiscs.open_disjoint hopposite hchosen
  · have heq : p.2 = a :=
      (sourceDisc_collar_mem_retained_iff e he E.data.sourceCollar sigma
        E.radius_mem.1 E.radius_mem.2 E.radius_near hk
        (by simpa only [e, sigma] using E.radial i) theta
        (le_of_not_gt hneg) hp.2.2.le).mp hretained
    exact hp.2.2.ne heq


theorem RegularSurgeryEvent.reunionTube_capMap
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2)
    (tau : ℝ) (q : UnitTwoSphere) :
    let a := E.data.width / 2 * (1 - E.radius)
    E.profile.capMap (E.reunionTube i) 0 tau a E.scale q =
      E.profile.capMap E.data.tube E.cutHeight
        ((![1, -1] i) * tau) a E.scale q := by
  dsimp only
  rw [SurgeryCapProfile.capMap_apply, (E.reunionTube_spec i).1,
    SurgeryCapProfile.capMap_apply]
  congr 1
  apply Prod.ext
  · rfl
  · ring


theorem RegularSurgeryEvent.reunion_region_identities
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2) :
    let a := E.data.width / 2 * (1 - E.radius)
    let sigma : ℝ := ![1, -1] i
    let other : Fin 2 := ![1, 0] i
    let T := E.reunionTube i
    let annulus := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - a) (E.cutHeight + a))
    let annulusClosed := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))
    let north := E.profile.capMap E.data.tube E.cutHeight (-sigma) a E.scale ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    E.profile.capMap T 0 1 a E.scale ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} =
        (E.newCap i).cap ∧
      T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ)) = (E.newCap i).seam ∧
      T '' (sphere (0 : E2) 1 ×ˢ ({-a} : Set ℝ)) = (E.newCap other).seam ∧
      (E.newCap i).seam = E.data.tube ''
        (sphere (0 : E2) 1 ×ˢ ({E.cutHeight + sigma * a} : Set ℝ)) ∧
      (E.newCap other).seam = E.data.tube ''
        (sphere (0 : E2) 1 ×ˢ ({E.cutHeight - sigma * a} : Set ℝ)) ∧
      T '' (sphere (0 : E2) 1 ×ˢ Ioo (-a) a) = annulus ∧
      T '' (sphere (0 : E2) 1 ×ˢ Icc (-a) a) = annulusClosed ∧
      annulusClosed = (E.newCap i).seam ∪ annulus ∪ (E.newCap other).seam ∧
      E.profile.capMap T 0 (-1) a E.scale ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} = north ∧
      E.profile.capMap E.data.tube E.cutHeight (-sigma) a E.scale ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} =
        (E.newCap other).seam ∧
      (E.newCap other).seam ⊆ north ∧
      north ∩ annulusClosed = (E.newCap other).seam := by
  let a := E.data.width / 2 * (1 - E.radius)
  let sigma : ℝ := ![1, -1] i
  let other : Fin 2 := ![1, 0] i
  let T := E.reunionTube i
  let annulus := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - a) (E.cutHeight + a))
  let annulusClosed := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Icc (E.cutHeight - a) (E.cutHeight + a))
  let north := E.profile.capMap E.data.tube E.cutHeight (-sigma) a E.scale ''
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  obtain ⟨_hdelta, ha, _hak, _hkd, hl, _hsmall⟩ := E.parameter_bounds
  change 0 < a at ha
  obtain ⟨happ, _hsourceEq, _htarget, _hinverse, hsource, _hT, _hTi, _hheight⟩ :=
    E.reunionTube_spec i
  have hother : (![1, -1] other : ℝ) = -sigma := by
    fin_cases i <;> norm_num [other, sigma]
  have hseam (j : Fin 2) : (E.newCap j).seam = E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ ({E.cutHeight + (![1, -1] j) * a} : Set ℝ)) := by
    obtain ⟨hP, hT, ht, hc, hlambda, hs⟩ := E.newCap_spec j
    rw [(E.newCap j).seam_eq_image, hP, hT, ht, hc, hlambda, hs]
    exact surgery_cap_equator_image E.profile E.data.tube E.cutHeight
      (![1, -1] j) a E.scale
  have hotherSeam : (E.newCap other).seam = E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ ({E.cutHeight - sigma * a} : Set ℝ)) := by
    simpa only [hother, neg_mul, ← sub_eq_add_neg] using hseam other
  have hcap : E.profile.capMap T 0 1 a E.scale ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} =
        (E.newCap i).cap := by
    obtain ⟨hP, hT, ht, hc, hlambda, hs⟩ := E.newCap_spec i
    rw [(E.newCap i).cap_eq_image, hP, hT, ht, hc, hlambda, hs]
    apply image_congr
    intro q _hq
    simpa only [mul_one] using E.reunionTube_capMap i 1 q
  have himage (I : Set ℝ) : T '' (sphere (0 : E2) 1 ×ˢ I) =
      E.data.tube '' (sphere (0 : E2) 1 ×ˢ
        ((fun z : ℝ => E.cutHeight + sigma * z) '' I)) := by
    ext y
    constructor
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
      exact ⟨(x, E.cutHeight + sigma * z), ⟨hx, ⟨z, hz, rfl⟩⟩,
        (happ (x, z)).symm⟩
    · rintro ⟨⟨x, h⟩, ⟨hx, ⟨z, hz, rfl⟩⟩, rfl⟩
      exact ⟨(x, z), ⟨hx, hz⟩, happ (x, z)⟩
  have hplus : T '' (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ)) =
      (E.newCap i).seam := by
    rw [himage, image_singleton]
    exact (hseam i).symm
  have hminus : T '' (sphere (0 : E2) 1 ×ˢ ({-a} : Set ℝ)) =
      (E.newCap other).seam := by
    rw [himage, image_singleton]
    simpa only [mul_neg, sub_eq_add_neg] using hotherSeam.symm
  have hIoo : (fun z : ℝ => E.cutHeight + sigma * z) '' Ioo (-a) a =
      Ioo (E.cutHeight - a) (E.cutHeight + a) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      fin_cases i <;> dsimp [sigma] <;> constructor <;> linarith only [hs.1, hs.2]
    · intro hz
      refine ⟨sigma * (z - E.cutHeight), ?_, ?_⟩
      · fin_cases i <;> dsimp [sigma] <;> constructor <;> linarith only [hz.1, hz.2]
      · fin_cases i <;> dsimp [sigma] <;> ring
  have hIcc : (fun z : ℝ => E.cutHeight + sigma * z) '' Icc (-a) a =
      Icc (E.cutHeight - a) (E.cutHeight + a) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      fin_cases i <;> dsimp [sigma] <;> constructor <;> linarith only [hs.1, hs.2]
    · intro hz
      refine ⟨sigma * (z - E.cutHeight), ?_, ?_⟩
      · fin_cases i <;> dsimp [sigma] <;> constructor <;> linarith only [hz.1, hz.2]
      · fin_cases i <;> dsimp [sigma] <;> ring
  have hannulus : T '' (sphere (0 : E2) 1 ×ˢ Ioo (-a) a) = annulus := by
    rw [himage, hIoo]
  have hclosed : T '' (sphere (0 : E2) 1 ×ˢ Icc (-a) a) = annulusClosed := by
    rw [himage, hIcc]
  have hsplit : sphere (0 : E2) 1 ×ˢ Icc (-a) a =
      (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ)) ∪
        (sphere (0 : E2) 1 ×ˢ Ioo (-a) a) ∪
        (sphere (0 : E2) 1 ×ˢ ({-a} : Set ℝ)) := by
    ext p
    simp only [mem_prod, mem_Icc, mem_union, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨hx, hlo, hhi⟩
      rcases eq_or_lt_of_le hhi with htop | htop
      · exact Or.inl (Or.inl ⟨hx, htop⟩)
      · rcases eq_or_lt_of_le hlo with hbottom | hbottom
        · exact Or.inr ⟨hx, hbottom.symm⟩
        · exact Or.inl (Or.inr ⟨hx, hbottom, htop⟩)
    · rintro ((⟨hx, htop⟩ | ⟨hx, hlo, hhi⟩) | ⟨hx, hbottom⟩)
      · exact ⟨hx, by rw [htop]; linarith only [ha], htop.le⟩
      · exact ⟨hx, hlo.le, hhi.le⟩
      · exact ⟨hx, hbottom.symm.le, by rw [hbottom]; linarith only [ha]⟩
  have hclosedUnion : annulusClosed =
      (E.newCap i).seam ∪ annulus ∪ (E.newCap other).seam := by
    rw [← hclosed, hsplit, image_union, image_union, hplus, hannulus, hminus]
  have hplaced (q : UnitTwoSphere) : E.profile.capMap T 0 (-1) a E.scale q =
      E.profile.capMap E.data.tube E.cutHeight (-sigma) a E.scale q := by
    simpa only [mul_neg_one] using E.reunionTube_capMap i (-1) q
  have hnorth : E.profile.capMap T 0 (-1) a E.scale ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} = north := by
    exact image_congr (fun q _hq => hplaced q)
  have hequator : E.profile.capMap E.data.tube E.cutHeight (-sigma) a E.scale ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} =
        (E.newCap other).seam := by
    rw [surgery_cap_equator_image]
    simpa only [neg_mul, sub_eq_add_neg] using hotherSeam.symm
  have hseamNorth : (E.newCap other).seam ⊆ north := by
    intro y hy
    rw [← hequator] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    exact ⟨q, hq.symm.le, rfl⟩
  have hinter : north ∩ annulusClosed = (E.newCap other).seam := by
    ext y
    constructor
    · rintro ⟨⟨q, hq, hqy⟩, hyAnnulus⟩
      rw [← hclosed] at hyAnnulus
      obtain ⟨p, hp, hpy⟩ := hyAnnulus
      let Z := (E.profile.model q).2
      have hZnonneg : 0 ≤ Z := by
        change 0 ≤ E.profile.vertical
          (E.profile.horizontal (heightCoordinates (q : E3)).2 •
            (heightCoordinates (q : E3)).1) * (heightCoordinates (q : E3)).2
        exact mul_nonneg (E.profile.vertical_pos _).le hq
      have hqsource : ((E.profile.model q).1,
          0 + (-1) * (a + E.scale * Z)) ∈ T.source :=
        hsource ⟨mem_closedBall_zero_iff.mpr (E.profile.model_fst_norm_le q), mem_univ _⟩
      have hpsource : p ∈ T.source :=
        hsource ⟨sphere_subset_closedBall hp.1, mem_univ _⟩
      have hpair : ((E.profile.model q).1, 0 + (-1) * (a + E.scale * Z)) = p :=
        T.injOn hqsource hpsource ((hplaced q).trans (hqy.trans hpy.symm))
      have hheight : -a - E.scale * Z = p.2 := by
        have h := congrArg Prod.snd hpair
        dsimp only at h
        linarith only [h]
      have hZ : Z = 0 := by
        nlinarith only [hp.2.1, hheight, hZnonneg, hl]
      have hqzero : (heightCoordinates (q : E3)).2 = 0 := by
        change E.profile.vertical
          (E.profile.horizontal (heightCoordinates (q : E3)).2 •
            (heightCoordinates (q : E3)).1) * (heightCoordinates (q : E3)).2 = 0 at hZ
        exact (mul_eq_zero.mp hZ).resolve_left (E.profile.vertical_pos _).ne'
      rw [← hequator]
      exact ⟨q, hqzero, hqy⟩
    · intro hy
      refine ⟨hseamNorth hy, ?_⟩
      rw [hclosedUnion]
      exact Or.inr hy
  exact ⟨hcap, hplus, hminus, hseam i, hotherSeam, hannulus, hclosed,
    hclosedUnion, hnorth, hequator, hseamNorth, hinter⟩

end PoincareConjecture.M25.Topology3D
