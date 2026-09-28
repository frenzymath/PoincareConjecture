import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCapEnds
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesCompactSide
import PoincareConjecture.Proofs.M25.Mathlib.CompactFrontierUniqueness











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capCertificate_exists_projective_buffered_ball_chart
    (hS : SchoenfliesService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g)
    (P : PoincareConjecture.StandardPuncturedProjectiveCover
      M C.puncture C.carrier)
    (c h : ℝ) (hh : 0 < h)
    (hleft : -C.epsilon⁻¹ < c - h)
    (hright : c + h < C.epsilon⁻¹) :
    let H := C.epsilon⁻¹
    let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-H) H
    ∃ (p0 : UnitThreeSphere) (F : RoundCylinderSpace → UnitThreeSphere),
      (Quotient.mk' p0 : RealProjectiveThree) = C.puncture ∧
      MapsTo F Omega (projectiveCoverDomain C.puncture) ∧
      EqOn (P.cover ∘ F) C.coordinate_map Omega ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ F Omega ∧
      InjOn F Omega ∧
      Disjoint (F '' Omega) ((fun z => -F z) '' Omega) ∧
      (∀ s ∈ Ioo (-H) H,
        let T : Set UnitThreeSphere := F '' (univ ×ˢ Ioo s H)
        let Sigma : Set UnitThreeSphere := F '' (univ ×ˢ ({s} : Set ℝ))
        let B : Set UnitThreeSphere := T ∪ {p0}
        IsOpen B ∧ IsConnected B ∧ IsCompact (closure B) ∧
        closure B = B ∪ Sigma ∧ interior (closure B) = B ∧
        frontier (closure B) = Sigma ∧
        Disjoint (closure B)
          ((fun x : UnitThreeSphere => -x) '' closure B) ∧
        projectiveCoverDomain C.puncture ∩
            P.cover ⁻¹' (C.carrier \ C.region s H) =
          (B ∪ (fun x : UnitThreeSphere => -x) '' B)ᶜ) ∧
      let theta := threeSphereStereographic (-p0)
      let B : ℝ → Set UnitThreeSphere :=
        fun s => F '' (univ ×ˢ Ioo s H) ∪ {p0}
      let a := c - h * (3 / 4)
      let b := c - h * (1 / 2)
      let psi := fun z : UnitTwoSphere × ℝ =>
        theta (F (z.1, c + h * z.2))
      IsCollarEmbedding psi ∧
      ∃ (S : SchoenfliesData psi (1 / 4))
        (J : OpenPartialHomeomorph UnitThreeSphere E3),
        S.side = -1 ∧
        (∀ s ∈ Ioo (-H) H, closure (B s) ⊆ theta.source) ∧
        (∀ t ∈ Ico (1 / 4 : ℝ) 1,
          theta '' closure (B (c - h * t)) =
              S.chart '' closedBall 0 (S.radial t) ∧
          theta '' B (c - h * t) = S.chart '' ball 0 (S.radial t)) ∧
        J.source = B a ∧ J.target = ball 0 (S.radial (3 / 4)) ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ J J.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ J.symm J.target ∧
        (J.symm : E3 → UnitThreeSphere) =
          (fun z => theta.symm (S.chart z)) ∧
        (∀ x ∈ J.source, S.chart (J x) = theta x) ∧
        J.source \ closure (B b) = F '' (univ ×ˢ Ioo a b) ∧
        J '' (F '' (univ ×ˢ Ioo a b)) =
          {z : E3 | S.radial (1 / 2) < ‖z‖ ∧ ‖z‖ < S.radial (3 / 4)} ∧
        J.symm '' {z : E3 |
          S.radial (1 / 2) < ‖z‖ ∧ ‖z‖ < S.radial (3 / 4)} =
          F '' (univ ×ˢ Ioo a b) ∧
        (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Ico (1 / 4) (3 / 4) →
          F (q, c - h * t) ∈ J.source ∧
          J (F (q, c - h * t)) = S.radial t • (S.boundary_map q).val) ∧
        (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (1 / 2) (3 / 4) →
          J.symm (S.radial t • (S.boundary_map q).val) = F (q, c - h * t)) := by
  classical
  obtain ⟨p0, F, hp0, hFD, hFc, hFloc, hFinj, hFdis, hends⟩ :=
    capCertificate_exists_projective_filled_end_lift C P
  let H := C.epsilon⁻¹
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-H) H
  let theta := threeSphereStereographic (-p0)
  let B : ℝ → Set UnitThreeSphere := fun s => F '' (univ ×ˢ Ioo s H) ∪ {p0}
  let Sigma : ℝ → Set UnitThreeSphere := fun s => F '' (univ ×ˢ ({s} : Set ℝ))
  let a := c - h * (3 / 4)
  let b := c - h * (1 / 2)
  let psi := fun z : UnitTwoSphere × ℝ => theta (F (z.1, c + h * z.2))
  have hpole : (Quotient.mk' (-p0) : RealProjectiveThree) = C.puncture :=
    (projectiveQuotient_neg p0).trans hp0
  have hFtheta : MapsTo F Omega theta.source :=
    (projective_collar_stereographic_control (-p0) hpole hFD hFloc hFinj).1
  have hpsi : IsCollarEmbedding psi :=
    (projective_collar_stereographic_normalized (-p0) hpole hFD hFloc hFinj
      c h hh hleft hright).1
  have hheight0 {s : ℝ} (hs : s ∈ Icc (c - h) (c + h)) : s ∈ Ioo (-H) H :=
    ⟨lt_of_lt_of_le hleft hs.1, lt_of_le_of_lt hs.2 hright⟩
  have ha : a ∈ Ioo (-H) H := hheight0 ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  have hb : b ∈ Ioo (-H) H := hheight0 ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  have hpB (s : ℝ) : p0 ∈ B s := Or.inr rfl
  have hsource (s : ℝ) (hs : s ∈ Ioo (-H) H) : closure (B s) ⊆ theta.source := by
    obtain ⟨_, _, _, _, _, _, hdis, _⟩ := hends s hs
    intro x hx
    rw [threeSphereStereographic_source]
    change x ≠ -p0
    intro heq
    exact (disjoint_left.mp hdis) hx ⟨p0, subset_closure (hpB s), heq.symm⟩
  have hFne {z : RoundCylinderSpace} (hz : z ∈ Omega) : F z ≠ p0 := by
    intro heq
    have hd := hFD hz
    change (Quotient.mk' (F z) : RealProjectiveThree) ≠ C.puncture at hd
    exact hd ((congrArg (fun x : UnitThreeSphere => (Quotient.mk' x : RealProjectiveThree))
      heq).trans hp0)
  have hmemB (s : ℝ) (hs : s ∈ Ioo (-H) H)
      (z : RoundCylinderSpace) (hz : z ∈ Omega) : F z ∈ B s ↔ s < z.2 := by
    constructor
    · rintro (hx | hx)
      · obtain ⟨w, hw, heq⟩ := hx
        have hwO : w ∈ Omega := ⟨mem_univ _, hs.1.trans hw.2.1, hw.2.2⟩
        have hwz := hFinj hwO hz heq
        simpa only [hwz] using hw.2.1
      · exact (hFne hz (mem_singleton_iff.mp hx)).elim
    · intro hsz
      exact Or.inl ⟨z, ⟨mem_univ _, hsz, hz.2.2⟩, rfl⟩
  have hmemQ (s : ℝ) (hs : s ∈ Ioo (-H) H)
      (z : RoundCylinderSpace) (hz : z ∈ Omega) :
      F z ∈ closure (B s) ↔ s ≤ z.2 := by
    obtain ⟨_, _, _, hcl, _, _, _, _⟩ := hends s hs
    rw [hcl]
    constructor
    · rintro (hx | hx)
      · exact ((hmemB s hs z hz).mp hx).le
      · obtain ⟨w, hw, heq⟩ := hx
        have hws : w.2 = s := mem_singleton_iff.mp hw.2
        have hwO : w ∈ Omega := ⟨mem_univ _, hws.symm ▸ hs⟩
        have hwz := hFinj hwO hz heq
        exact le_of_eq ((congrArg Prod.snd hwz).symm.trans hws).symm
    · intro hsz
      rcases lt_or_eq_of_le hsz with hlt | heq
      · exact Or.inl ((hmemB s hs z hz).mpr hlt)
      · exact Or.inr ⟨z, ⟨mem_univ _, mem_singleton_iff.mpr heq.symm⟩, rfl⟩
  have htop (s : ℝ) (hs : s ∈ Ioo (-H) H) :
      interior (theta '' closure (B s)) = theta '' B s ∧
      frontier (theta '' closure (B s)) = theta '' Sigma s := by
    obtain ⟨_, _, _, _, hi, hf, _, _⟩ := hends s hs
    have him : theta.IsImage (closure (B s)) (theta '' closure (B s)) := by
      intro x hx
      constructor
      · rintro ⟨y, hy, heq⟩
        exact theta.injOn (hsource s hs hy) hx heq ▸ hy
      · intro hxQ
        exact mem_image_of_mem theta hxQ
    have hiSub : interior (closure (B s)) ⊆ theta.source :=
      interior_subset.trans (hsource s hs)
    have hfSub : frontier (closure (B s)) ⊆ theta.source := by
      exact (frontier_subset_closure.trans (by rw [closure_closure]; exact hsource s hs))
    have hiEq := him.interior.image_eq
    have hfEq := him.frontier.image_eq
    rw [inter_eq_right.mpr hiSub, threeSphereStereographic_target, univ_inter, hi] at hiEq
    rw [inter_eq_right.mpr hfSub, threeSphereStereographic_target, univ_inter, hf] at hfEq
    exact ⟨hiEq.symm, hfEq.symm⟩
  obtain ⟨S⟩ := hS psi hpsi (1 / 4) (by norm_num) (by norm_num)
  have hheight (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      c + h * (S.side * t) ∈ Ioo (-H) H := by
    apply hheight0
    rcases mul_self_eq_one_iff.mp S.side_sq with hs | hs
    · rw [hs, one_mul]
      constructor <;> nlinarith [ht.1, ht.2]
    · rw [hs, neg_one_mul]
      constructor <;> nlinarith [ht.1, ht.2]
  have hballs (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      theta '' closure (B (c + h * (S.side * t))) =
        S.chart '' closedBall 0 (S.radial t) := by
    let s := c + h * (S.side * t)
    have hs := hheight t ht
    have hK : IsCompact (theta '' closure (B s)) :=
      (hends s hs).2.2.1.image_of_continuousOn (theta.continuousOn.mono (hsource s hs))
    have hBi : IsPreconnected (interior (S.chart '' closedBall 0 (S.radial t))) := by
      rw [S.interior_chart_closedBall ht]
      exact isPreconnected_ball.image S.chart
        (S.chart_smooth.continuousOn.mono (ball_subset_ball (S.radial_lt t ht).le))
    have hne : (interior (theta '' closure (B s))).Nonempty := by
      rw [(htop s hs).1]
      exact ⟨theta p0, mem_image_of_mem theta (hpB s)⟩
    have hf : frontier (theta '' closure (B s)) =
        frontier (S.chart '' closedBall 0 (S.radial t)) := by
      rw [(htop s hs).2, S.frontier_chart_closedBall ht, S.image_sphere_eq_collar_level ht]
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have hzs : z.2 = s := mem_singleton_iff.mp hz.2
        refine ⟨z.1, mem_univ _, ?_⟩
        change theta (F (z.1, s)) = theta (F z)
        rw [← hzs]
      · rintro ⟨q, _, rfl⟩
        exact ⟨F (q, s), ⟨(q, s), ⟨mem_univ _, mem_singleton s⟩, rfl⟩, rfl⟩
    exact IsCompact.eq_of_frontier_eq_of_preconnected_interior_compl
      (NormedSpace.unbounded_univ ℝ E3) hK (S.isCompact_chart_closedBall ht) hBi
      (S.isConnected_compl_chart_closedBall ht).isPreconnected hne hf
  have htm : (3 / 4 : ℝ) ∈ Ico (1 / 4 : ℝ) 1 := by norm_num
  have htl : (1 / 2 : ℝ) ∈ Ico (1 / 4 : ℝ) 1 := by norm_num
  have hside : S.side = -1 := by
    rcases mul_self_eq_one_iff.mp S.side_sq with hs | hs
    · let q := (C.coordinate_inverse C.endCenter).1
      have hz : (q, c + h * (1 / 2)) ∈ Omega := by
        refine ⟨mem_univ _, ?_⟩
        simpa only [hs, one_mul] using hheight (1 / 2) htl
      have hxB : theta (F (q, c + h * (1 / 2))) ∈
          S.chart '' closedBall 0 (S.radial (3 / 4)) := by
        refine ⟨S.radial (1 / 2) • (S.boundary_map q).val, ?_, ?_⟩
        · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
            mem_sphere_zero_iff_norm.mp (S.boundary_map q).property,
            mul_one, abs_of_pos (S.radial_pos _ htl)]
          exact (S.radial_strictMono htl htm (by norm_num)).le
        · simpa only [hs, one_mul] using S.chart_collar q (1 / 2) htl
      have heq := hballs (3 / 4) htm
      have hh1 := hheight (3 / 4) htm
      rw [hs, one_mul] at heq hh1
      obtain ⟨y, hy, hyx⟩ := heq.symm ▸ hxB
      have hyx' := theta.injOn (hsource _ hh1 hy) (hFtheta hz) hyx
      have hxQ : F (q, c + h * (1 / 2)) ∈ closure (B (c + h * (3 / 4))) := hyx' ▸ hy
      have hle := (hmemQ _ hh1 _ hz).mp hxQ
      exfalso
      dsimp only at hle
      linarith
    · exact hs
  have hminus (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      c - h * t ∈ Ioo (-H) H := by
    simpa only [hside, neg_one_mul, mul_neg, ← sub_eq_add_neg] using hheight t ht
  have himages (t : ℝ) (ht : t ∈ Ico (1 / 4 : ℝ) 1) :
      theta '' closure (B (c - h * t)) = S.chart '' closedBall 0 (S.radial t) ∧
      theta '' B (c - h * t) = S.chart '' ball 0 (S.radial t) := by
    have hclosed := hballs t ht
    simp only [hside, neg_one_mul, mul_neg, ← sub_eq_add_neg] at hclosed
    refine ⟨hclosed, ?_⟩
    have hi := congrArg interior hclosed
    rw [(htop _ (hminus t ht)).1, S.interior_chart_closedBall ht] at hi
    exact hi
  let rm := S.radial (3 / 4)
  let rl := S.radial (1 / 2)
  have hrlt : rm < S.radius := S.radial_lt _ htm
  have hrlm : rl < rm := S.radial_strictMono htl htm (by norm_num)
  obtain ⟨D, hDs, _, hDf, _, hDi⟩ := S.exists_chart_openPartialHomeomorph
  let Dm := D.restrOpen (ball 0 rm) isOpen_ball
  have hDmSub : ball (0 : E3) rm ⊆ D.source := by
    rw [hDs]
    exact ball_subset_ball hrlt.le
  have hDms : Dm.source = ball 0 rm := inter_eq_right.mpr hDmSub
  have hDmf : (Dm : E3 → E3) = S.chart := hDf
  have hDmt : Dm.target = S.chart '' ball 0 rm := by
    rw [← Dm.image_source_eq_target, hDms, hDmf]
  let J := (Dm.trans theta.symm).symm
  have hJt : J.target = ball 0 rm := by
    change Dm.source ∩ Dm ⁻¹' theta.target = ball 0 rm
    rw [threeSphereStereographic_target, preimage_univ, inter_univ, hDms]
  have hJi : (J.symm : E3 → UnitThreeSphere) = fun z => theta.symm (S.chart z) := by
    funext z
    change theta.symm (Dm z) = theta.symm (S.chart z)
    rw [hDmf]
  have hJs : J.source = B a := by
    have heq : J.symm '' J.target = B a := by
      rw [hJi, hJt]
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have him : S.chart z ∈ theta '' B a :=
          (himages (3 / 4) htm).2.symm ▸ mem_image_of_mem S.chart hz
        obtain ⟨y, hy, heq⟩ := him
        have hh := congrArg theta.symm heq
        rw [theta.left_inv (hsource a ha (subset_closure hy))] at hh
        change theta.symm (S.chart z) ∈ B a
        exact hh ▸ hy
      · intro hx
        have him : theta x ∈ S.chart '' ball 0 rm :=
          (himages (3 / 4) htm).2 ▸ mem_image_of_mem theta hx
        obtain ⟨z, hz, heq⟩ := him
        refine ⟨z, hz, ?_⟩
        change theta.symm (S.chart z) = x
        rw [heq, theta.left_inv (hsource a ha (subset_closure hx))]
    exact J.symm.image_source_eq_target.symm.trans heq
  have hJsub : J.source ⊆ theta.source := by
    rw [hJs]
    exact subset_closure.trans (hsource a ha)
  have hJf (x : UnitThreeSphere) (hx : x ∈ J.source) : S.chart (J x) = theta x := by
    have hi := congrArg theta (J.left_inv hx)
    rw [hJi, theta.right_inv (by rw [threeSphereStereographic_target]; trivial)] at hi
    exact hi
  have htheta := threeSphereStereographic_mem_maximalAtlas (-p0)
  have hJsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J J.source := by
    have hDmi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Dm.symm Dm.target :=
      hDi.contMDiffOn.mono (fun z hz => by
        obtain ⟨w, hw, rfl⟩ := Dm.image_source_eq_target.symm ▸ hz
        exact D.map_source hw.1)
    apply hDmi.comp ((contMDiffOn_of_mem_maximalAtlas htheta).mono hJsub)
    intro x hx
    change theta x ∈ Dm.target
    rw [hDmt, ← hJf x hx]
    exact mem_image_of_mem S.chart (hJt ▸ J.map_source hx)
  have hJismooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J.symm J.target := by
    rw [hJi, hJt]
    apply (contMDiffOn_symm_of_mem_maximalAtlas htheta).comp
      (S.chart_smooth.mono (ball_subset_ball hrlt.le)).contMDiffOn
    intro z _
    rw [threeSphereStereographic_target]
    exact mem_univ _
  have hdiff : J.source \ closure (B b) = F '' (univ ×ˢ Ioo a b) := by
    rw [hJs]
    ext x
    constructor
    · rintro ⟨hx, hnot⟩
      rcases hx with hx | hx
      · obtain ⟨z, hz, rfl⟩ := hx
        have hzO : z ∈ Omega := ⟨mem_univ _, ha.1.trans hz.2.1, hz.2.2⟩
        exact ⟨z, ⟨mem_univ _, hz.2.1,
          lt_of_not_ge (fun hle => hnot ((hmemQ b hb z hzO).mpr hle))⟩, rfl⟩
      · exact (hnot ((mem_singleton_iff.mp hx).symm ▸ subset_closure (hpB b))).elim
    · rintro ⟨z, hz, rfl⟩
      have hzO : z ∈ Omega := ⟨mem_univ _, ha.1.trans hz.2.1, hz.2.2.trans hb.2⟩
      exact ⟨(hmemB a ha z hzO).mpr hz.2.1,
        fun hq => (not_le_of_gt hz.2.2) ((hmemQ b hb z hzO).mp hq)⟩
  have hQb (x : UnitThreeSphere) (hx : x ∈ J.source) :
      x ∈ closure (B b) ↔ J x ∈ closedBall 0 rl := by
    constructor
    · intro hxb
      have him := (himages (1 / 2) htl).1 ▸ mem_image_of_mem theta hxb
      obtain ⟨z, hz, heq⟩ := him
      have hzS : z ∈ ball (0 : E3) S.radius :=
        closedBall_subset_ball (hrlm.trans hrlt) hz
      have hxS : J x ∈ ball (0 : E3) S.radius :=
        ball_subset_ball hrlt.le (hJt ▸ J.map_source hx)
      have he := S.chart_injOn hxS hzS ((hJf x hx).trans heq.symm)
      exact he.symm ▸ hz
    · intro hxr
      have him : theta x ∈ S.chart '' closedBall 0 rl := ⟨J x, hxr, hJf x hx⟩
      obtain ⟨y, hy, heq⟩ := (himages (1 / 2) htl).1.symm ▸ him
      exact theta.injOn (hsource b hb hy) (hJsub hx) heq ▸ hy
  have hannulus : J '' (F '' (univ ×ˢ Ioo a b)) =
      {z : E3 | rl < ‖z‖ ∧ ‖z‖ < rm} := by
    rw [← hdiff]
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hnot⟩, rfl⟩
      refine ⟨?_, mem_ball_zero_iff.mp (hJt ▸ J.map_source hx)⟩
      exact lt_of_not_ge (fun hle => hnot ((hQb x hx).mpr (mem_closedBall_zero_iff.mpr hle)))
    · intro hz
      have hzJ : z ∈ J.target := hJt.symm ▸ mem_ball_zero_iff.mpr hz.2
      have hxJ := J.map_target hzJ
      refine ⟨J.symm z, ⟨hxJ, ?_⟩, J.right_inv hzJ⟩
      intro hxQ
      have hnorm := (hQb (J.symm z) hxJ).mp hxQ
      rw [J.right_inv hzJ] at hnorm
      exact (not_le_of_gt hz.1) (mem_closedBall_zero_iff.mp hnorm)
  have hannulusInv : J.symm '' {z : E3 | rl < ‖z‖ ∧ ‖z‖ < rm} =
      F '' (univ ×ˢ Ioo a b) := by
    rw [← hannulus]
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      rw [J.left_inv ((hdiff.symm ▸ hy).1)]
      exact hy
    · intro hx
      exact ⟨J x, mem_image_of_mem J hx, J.left_inv ((hdiff.symm ▸ hx).1)⟩
  refine ⟨p0, F, hp0, hFD, hFc, hFloc, hFinj, hFdis, hends, hpsi,
    S, J, hside, hsource, himages, hJs, hJt, hJsmooth, hJismooth,
    hJi, hJf, hdiff, hannulus, hannulusInv, ?_, ?_⟩
  · intro q t ht
    have ht1 : t ∈ Ico (1 / 4 : ℝ) 1 := ⟨ht.1, ht.2.trans (by norm_num)⟩
    have hr : S.radial t • (S.boundary_map q).val ∈ J.target := by
      rw [hJt, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp (S.boundary_map q).property,
        mul_one, abs_of_pos (S.radial_pos t ht1)]
      exact S.radial_strictMono ht1 htm ht.2
    have hi : J.symm (S.radial t • (S.boundary_map q).val) = F (q, c - h * t) := by
      rw [hJi]
      dsimp only
      rw [S.chart_collar q t ht1]
      change theta.symm (theta (F (q, c + h * (S.side * t)))) = _
      rw [theta.left_inv (hFtheta ⟨mem_univ _, hheight t ht1⟩)]
      simp only [hside, neg_one_mul, mul_neg, ← sub_eq_add_neg]
    refine ⟨hi ▸ J.map_target hr, ?_⟩
    rw [← hi, J.right_inv hr]
  · intro q t ht
    have ht1 : t ∈ Ico (1 / 4 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hJi]
    dsimp only
    rw [S.chart_collar q t ht1]
    change theta.symm (theta (F (q, c + h * (S.side * t)))) = _
    rw [theta.left_inv (hFtheta ⟨mem_univ _, hheight t ht1⟩)]
    simp only [hside, neg_one_mul, mul_neg, ← sub_eq_add_neg]

end PoincareConjecture.M25.Topology3D
