import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCollarStereographic
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesCompactSide










set_option autoImplicit false

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 800000 in




theorem exists_antipodal_buffered_ball_chart_of_collar
    (hS : SchoenfliesService)
    (F : UnitTwoSphere × ℝ → UnitThreeSphere)
    (hFloc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      F (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hFinj : InjOn F (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hdis : Disjoint (F '' (univ ×ˢ Ioo (-1 : ℝ) 1))
      ((fun z => -F z) '' (univ ×ˢ Ioo (-1 : ℝ) 1)))
    (q0 : UnitTwoSphere) :
    let pole := -F (q0, 0)
    let theta := threeSphereStereographic pole
    let psi := fun z : UnitTwoSphere × ℝ => theta (F z)
    IsCollarEmbedding psi ∧
    ∃ (S : SchoenfliesData psi (1 / 4))
      (e : OpenPartialHomeomorph E3 UnitThreeSphere),
      e.source = ball 0 (S.radial (7 / 8)) ∧
      e.target = (fun x : E3 => theta.symm (S.chart x)) ''
        ball 0 (S.radial (7 / 8)) ∧
      (e : E3 → UnitThreeSphere) =
        (fun x => theta.symm (S.chart x)) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      Disjoint e.target ((fun x : UnitThreeSphere => -x) '' e.target) ∧
      (∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (1 / 4) (7 / 8) →
        e (S.radial t • (S.boundary_map q).val) = F (q, S.side * t) ∧
        e.symm (F (q, S.side * t)) =
          S.radial t • (S.boundary_map q).val) ∧
      (∀ t ∈ Icc (1 / 4 : ℝ) (7 / 8),
        let K := e '' closedBall 0 (S.radial t)
        IsCompact K ∧ IsConnected K ∧
        interior K = e '' ball 0 (S.radial t) ∧
        frontier K = F '' (univ ×ˢ ({S.side * t} : Set ℝ)) ∧
        Disjoint K ((fun x : UnitThreeSphere => -x) '' K)) := by
  classical
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-1 : ℝ) 1
  let pole := -F (q0, 0)
  let theta := threeSphereStereographic pole
  let psi := fun z : UnitTwoSphere × ℝ => theta (F z)
  have hq0 : (q0, 0) ∈ Omega := ⟨mem_univ _, by norm_num, by norm_num⟩
  have hsource : MapsTo F Omega theta.source := by
    intro z hz
    rw [threeSphereStereographic_source]
    change F z ≠ pole
    intro heq
    exact disjoint_left.mp hdis ⟨z, hz, rfl⟩ ⟨(q0, 0), hq0, heq.symm⟩
  have hploc : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞
      psi Omega := by
    intro z
    exact (hFloc z).comp 𝓘(ℝ, E3) E3
      (threeSphereStereographic_isLocalDiffeomorphOn pole ⟨F z.1, hsource z.2⟩)
  have hpsi : IsCollarEmbedding psi := by
    refine ⟨hploc.contMDiffOn, ?_, ?_⟩
    · intro z hz w hw heq
      exact hFinj hz hw (theta.injOn (hsource hz) (hsource hw) heq)
    · intro z hz
      exact ((hploc ⟨z, hz⟩).mfderivToContinuousLinearEquiv (by simp)).injective
  obtain ⟨S⟩ := hS psi hpsi (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨D, hDs, _, hDf, hDd, hDi⟩ := S.exists_chart_openPartialHomeomorph
  let P := D.trans theta.symm
  have hPs : P.source = ball 0 S.radius := by
    change D.source ∩ D ⁻¹' theta.target = ball 0 S.radius
    rw [threeSphereStereographic_target, preimage_univ, inter_univ, hDs]
  have hPf : (P : E3 → UnitThreeSphere) = fun x => theta.symm (S.chart x) := by
    funext x
    change theta.symm (D x) = theta.symm (S.chart x)
    rw [hDf]
  have hPt : P.target ⊆ theta.source := fun _ hx => hx.1
  have hPtheta (x : UnitThreeSphere) (hx : x ∈ P.target) : theta x ∈ D.target := hx.2
  have hatlas := threeSphereStereographic_mem_maximalAtlas pole
  have hPd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ P P.source := by
    rw [hPf, hPs]
    apply (contMDiffOn_symm_of_mem_maximalAtlas hatlas).comp S.chart_smooth.contMDiffOn
    intro x _
    rw [threeSphereStereographic_target]
    exact mem_univ _
  have hPid : ContMDiffOn (𝓡 3) (𝓡 3) ∞ P.symm P.target := by
    exact hDi.contMDiffOn.comp
      ((contMDiffOn_of_mem_maximalAtlas hatlas).mono hPt) hPtheta
  have htall {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      t ∈ Ico (1 / 4 : ℝ) 1 := ⟨ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩
  have hsigned {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      S.side * t ∈ Ioo (-1 : ℝ) 1 := by
    rcases mul_self_eq_one_iff.mp S.side_sq with hs | hs
    · rw [hs, one_mul]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · rw [hs, neg_one_mul]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hvec (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      S.radial t • (S.boundary_map q).val ∈ P.source := by
    rw [hPs, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp (S.boundary_map q).property, mul_one,
      abs_of_pos (S.radial_pos t (htall ht))]
    exact S.radial_lt t (htall ht)
  have hPray (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (1 / 4) (7 / 8)) :
      P (S.radial t • (S.boundary_map q).val) = F (q, S.side * t) := by
    rw [hPf]
    change theta.symm (S.chart (S.radial t • (S.boundary_map q).val)) = _
    rw [S.chart_collar q t (htall ht)]
    exact theta.left_inv (hsource ⟨mem_univ _, hsigned ht⟩)
  let e := P.restrOpen (ball 0 (S.radial (7 / 8))) isOpen_ball
  have houter : (7 / 8 : ℝ) ∈ Icc (1 / 4 : ℝ) (7 / 8) := by norm_num
  have hesub : ball (0 : E3) (S.radial (7 / 8)) ⊆ P.source := by
    rw [hPs]
    exact ball_subset_ball (S.radial_lt _ (htall houter)).le
  have hes : e.source = ball 0 (S.radial (7 / 8)) := inter_eq_right.mpr hesub
  have hef : (e : E3 → UnitThreeSphere) = (P : E3 → UnitThreeSphere) := rfl
  have hei : (e.symm : UnitThreeSphere → E3) = (P.symm : UnitThreeSphere → E3) := rfl
  have hetsub : e.target ⊆ P.target := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := e.image_source_eq_target.symm ▸ hx
    exact P.map_source hy.1
  have het : e.target = (fun x : E3 => theta.symm (S.chart x)) ''
      ball 0 (S.radial (7 / 8)) := by
    rw [← e.image_source_eq_target, hes, hef, hPf]
  have hed : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := hPd.mono inter_subset_left
  have heid : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := hPid.mono hetsub
  have hray (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (1 / 4) (7 / 8)) :
      e (S.radial t • (S.boundary_map q).val) = F (q, S.side * t) ∧
      e.symm (F (q, S.side * t)) = S.radial t • (S.boundary_map q).val := by
    refine ⟨hPray q t ht, ?_⟩
    rw [hei, ← hPray q t ht]
    exact P.left_inv (hvec q ht)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let N : UnitThreeSphere ≃ₜ UnitThreeSphere :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := neg_neg
      right_inv := neg_neg
      continuous_toFun := (contMDiff_neg_sphere (n := 3) (m := ∞)).continuous
      continuous_invFun := (contMDiff_neg_sphere (n := 3) (m := ∞)).continuous }
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let A := F '' Omega
  let AN := (fun z => -F z) '' Omega
  have hOc : IsConnected Omega := isConnected_univ.prod
    ((convex_Ioo (-1 : ℝ) 1).isConnected (nonempty_Ioo.mpr (by norm_num)))
  have hANc : IsConnected AN := hOc.image (fun z => -F z)
    (N.continuous.comp_continuousOn hFloc.contMDiffOn.continuousOn)
  have hpAN : pole ∈ AN := ⟨(q0, 0), hq0, rfl⟩
  have hballs (t : ℝ) (ht : t ∈ Icc (1 / 4 : ℝ) (7 / 8)) :
      let K := e '' closedBall 0 (S.radial t)
      IsCompact K ∧ IsConnected K ∧
      interior K = e '' ball 0 (S.radial t) ∧
      frontier K = F '' (univ ×ˢ ({S.side * t} : Set ℝ)) ∧
      Disjoint K ((fun x : UnitThreeSphere => -x) '' K) := by
    let K := e '' closedBall 0 (S.radial t)
    have hrt := S.radial_pos t (htall ht)
    have hrR := S.radial_lt t (htall ht)
    have hK : IsCompact K := P.isCompact_image_closedBall hPs hrR
    have hKc : IsConnected K :=
      ((convex_closedBall (0 : E3) (S.radial t)).isConnected
        (nonempty_closedBall.mpr hrt.le)).image P
        (P.continuousOn.mono (by rw [hPs]; exact closedBall_subset_ball hrR))
    have hKi : interior K = e '' ball 0 (S.radial t) :=
      P.interior_image_closedBall hPs hrt hrR
    have hKf : frontier K = F '' (univ ×ˢ ({S.side * t} : Set ℝ)) := by
      rw [show K = P '' closedBall 0 (S.radial t) from rfl,
        P.frontier_image_closedBall hPs hrt hrR, hPf]
      rw [show (fun x : E3 => theta.symm (S.chart x)) = theta.symm ∘ S.chart from rfl,
        image_comp, S.image_sphere_eq_collar_level (htall ht)]
      ext x
      constructor
      · rintro ⟨_, ⟨q, _, rfl⟩, rfl⟩
        refine ⟨(q, S.side * t), ⟨mem_univ _, mem_singleton _⟩, ?_⟩
        exact (theta.left_inv (hsource ⟨mem_univ _, hsigned ht⟩)).symm
      · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
        have hst : s = S.side * t := hs
        subst s
        exact ⟨psi (q, S.side * t), ⟨q, mem_univ _, rfl⟩,
          theta.left_inv (hsource ⟨mem_univ _, hsigned ht⟩)⟩
    have hfrontA : frontier K ⊆ A := by
      rw [hKf]
      rintro x ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      have hst : s = S.side * t := hs
      exact ⟨(q, s), ⟨mem_univ _, hst.symm ▸ hsigned ht⟩, rfl⟩
    have hpK : pole ∉ K := by
      intro hx
      have hh := hPt (P.image_closedBall_subset_target hPs hrR hx)
      rw [threeSphereStereographic_source] at hh
      exact hh rfl
    have hANavoid : Disjoint AN (frontier K) :=
      disjoint_left.mpr fun _ hx hy => disjoint_left.mp hdis (hfrontA hy) hx
    have hANcover : AN ⊆ interior K ∪ Kᶜ := by
      intro x hx
      by_cases hi : x ∈ interior K
      · exact Or.inl hi
      · exact Or.inr fun hk => disjoint_left.mp hANavoid hx ⟨subset_closure hk, hi⟩
    have hANout : AN ⊆ Kᶜ := by
      rcases hANc.isPreconnected.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
          (disjoint_left.mpr fun _ hx hy => hy (interior_subset hx)) hANcover with hi | ho
      · exact (hpK (interior_subset (hi hpAN))).elim
      · exact ho
    have hAout : A ⊆ (N '' K)ᶜ := by
      rintro x ⟨z, hz, rfl⟩ ⟨y, hy, heq⟩
      have hny : -F z = y := by
        have hh := congrArg (fun v : UnitThreeSphere => -v) heq
        change -(-y) = -F z at hh
        simpa only [neg_neg] using hh.symm
      exact hANout ⟨z, hz, hny⟩ hy
    have hNK : IsCompact (N '' K) := hK.image N.continuous
    have hNfront : frontier (N '' K) ⊆ AN := by
      rw [← N.image_frontier]
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hfrontA hy
      exact ⟨z, hz, rfl⟩
    have hKcover : K ⊆ interior (N '' K) ∪ (N '' K)ᶜ := by
      intro x hx
      by_cases hi : x ∈ interior (N '' K)
      · exact Or.inl hi
      · exact Or.inr fun hn => hANout (hNfront ⟨subset_closure hn, hi⟩) hx
    have hwfront : F (q0, S.side * t) ∈ frontier K := by
      rw [hKf]
      exact ⟨(q0, S.side * t), ⟨mem_univ _, mem_singleton _⟩, rfl⟩
    have hKout : K ⊆ (N '' K)ᶜ := by
      rcases hKc.isPreconnected.subset_or_subset isOpen_interior hNK.isClosed.isOpen_compl
          (disjoint_left.mpr fun _ hx hy => hy (interior_subset hx)) hKcover with hi | ho
      · exact (hAout (hfrontA hwfront)
          (interior_subset (hi (hK.isClosed.frontier_subset hwfront)))).elim
      · exact ho
    exact ⟨hK, hKc, hKi, hKf, disjoint_left.mpr fun _ hx hy => hKout hx hy⟩
  have hetK : e.target ⊆ e '' closedBall 0 (S.radial (7 / 8)) := by
    rw [← e.image_source_eq_target, hes]
    exact image_mono ball_subset_closedBall
  have hedis : Disjoint e.target ((fun x : UnitThreeSphere => -x) '' e.target) :=
    ((hballs (7 / 8) houter).2.2.2.2).mono hetK (image_mono hetK)
  exact ⟨hpsi, S, e, hes, het, hef.trans hPf, hed, heid, hedis, hray, hballs⟩

end PoincareConjecture.M25.Topology3D
