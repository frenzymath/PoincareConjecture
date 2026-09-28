import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerSourceSublevel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.TwoProfileEndBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in



theorem exists_saddle_nested_inner_end_scale_bound
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (i o : Fin 2) (hio : i ≠ o)
    (hnested : (W.disc i).closedRegion ⊆ (W.disc o).inside)
    (P : SurgeryCapProfile) (tau : ℝ) (htau : 0 < tau)
    (T : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
    (gamma : Fin 2 → ℝ) (hgamma : ∀ k, 0 < gamma k)
    (hs : ∀ k, closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T k).source)
    (hT : ∀ k, ContDiffOn ℝ ∞ (T k) (T k).source)
    (hTi : ∀ k, ContDiffOn ℝ ∞ (T k).symm (T k).target)
    (hh : ∀ k p, p ∈ (T k).source → ⟪(u : E3), T k p⟫_ℝ = p.2)
    (hold : ∀ k (q : UnitTwoSphere), (heightCoordinates (q : E3)).2 ≤ 0 →
      T k (((D.cap (W.label k)).profile.model q).1,
        (D.cap (W.label k)).cutHeight + (D.cap (W.label k)).removal +
          (D.cap (W.label k)).scale * ((D.cap (W.label k)).profile.model q).2) =
        psi ((D.cap (W.label k)).sourceChart q, 0))
    (hcircle : ∀ k t, t ∈ Icc
        ((D.cap (W.label k)).cutHeight + (D.cap (W.label k)).removal)
        (W.level + gamma k) →
      T k '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) =
        range (fun q : UnitCircle => psi (W.leg k (q, t), 0)))
    (hdisc : ∀ k,
      T k '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
        (fun x : E2 => (heightPlaneCoordinates u).symm (x, W.level)) ''
          (W.disc k).closedRegion) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S : Set E3 := range j
    let R : Set E3 := S ∩ {y : E3 | W.level ≤ H y}
    let ell : Fin 2 → ℝ := fun k =>
      (D.cap (W.label k)).cutHeight + (D.cap (W.label k)).removal
    let E : Fin 2 → Set E3 := fun k => j ''
      ((D.cap (W.label k)).sourceCap ∪
        W.leg k '' (univ ×ˢ Icc (ell k) W.level))
    ∃ d : ℝ, 0 < d ∧ d < tau ∧ d < W.level - ell i ∧
      ∀ lambda : ℝ, 0 < lambda → lambda * P.heightBound < d →
      let north : Set E3 :=
        (fun q : UnitTwoSphere => T i
          ((P.model q).1, W.level + lambda * (P.model q).2)) ''
            {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
      let rim : Set E3 := T i ''
        (sphere (0 : E2) 1 ×ˢ ({W.level} : Set ℝ))
      ∃ (Q : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
        (A : BallNeighborhoodChart E3 E3) (ov : ℝ),
        0 < ov ∧ ov < 1 / 4 ∧
        A.chart = Q.toHomeomorph.toOpenPartialHomeomorph.trans (T i) ∧
        A.chart.source = Q ⁻¹' (T i).source ∧ A.chart.target = (T i).target ∧
        (∀ y : E3, A.chart y = T i (Q y)) ∧
        (∀ y : E3, A.chart.symm y = Q.symm ((T i).symm y)) ∧
        A.boundary = E i ∪ north ∧
        A.inside ⊆ T i '' (ball (0 : E2) 1 ×ˢ (univ : Set ℝ)) ∧
        A.closedRegion ⊆ T i '' (closedBall (0 : E2) 1 ×ˢ
          Icc (ell i - (D.cap (W.label i)).scale *
            (D.cap (W.label i)).profile.heightBound)
            (W.level + lambda * P.heightBound)) ∧
        (∀ t ∈ Icc (ell i) W.level,
          A.inside ∩ {y : E3 | H y = t} =
            T i '' (ball (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ∧
          A.closedRegion ∩ {y : E3 | H y = t} =
            T i '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ))) ∧
        (∀ q : UnitTwoSphere, -ov < (heightCoordinates (q : E3)).2 →
          T i ((P.model q).1, W.level + lambda * (P.model q).2) ∈ A.boundary) ∧
        Disjoint A.inside S ∧ Disjoint A.closedRegion (E o) ∧
        A.closedRegion ∩ (R ∪ E o) ⊆ north ∧ E i ∩ north = rim := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  change ∀ k p, p ∈ (T k).source → H (T k p) = p.2 at hh
  let f : UnitTwoSphere → ℝ := fun q => H (j q)
  let z := W.level
  let S : Set E3 := range j
  let R : Set E3 := S ∩ {y : E3 | z ≤ H y}
  let ell : Fin 2 → ℝ := fun k =>
    (D.cap (W.label k)).cutHeight + (D.cap (W.label k)).removal
  let Lg : Fin 2 → Set UnitTwoSphere := fun k =>
    W.leg k '' (univ ×ˢ Icc (ell k) z)
  let Es : Fin 2 → Set UnitTwoSphere := fun k => (D.cap (W.label k)).sourceCap ∪ Lg k
  let E : Fin 2 → Set E3 := fun k => j '' Es k
  let rim : Fin 2 → Set E3 := fun k => T k '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))
  let Dtop : Set E3 := T i '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  have hf : Continuous f := H.continuous.comp hj
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      (show (p, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 by norm_num)
      (show (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 by norm_num) hpq)
  obtain ⟨_, hsub, hEs, hEsdis⟩ :=
    SaddleLowerLevelData.source_sublevel_decomposition psi hpsi u D W
  change {q : UnitTwoSphere | f q ≤ z} = ⋃ k : Fin 2, Es k at hsub
  change Disjoint (Es 0) (Es 1) at hEsdis
  have hell (k : Fin 2) : ell k < z := by
    simpa only [ell, W.label_lower k, one_mul] using
      W.lower_seams_lt_level (W.label k) (W.label_lower k)
  have hlegsource (k : Fin 2) : univ ×ˢ Icc (ell k) z ⊆ (W.leg k).source := by
    simpa only [ell, W.label_lower k, one_mul] using W.leg_source k
  have hES (k : Fin 2) : E k ⊆ S := by
    rintro y ⟨q, _, rfl⟩
    exact mem_range_self q
  have hEh (k : Fin 2) (y : E3) (hy : y ∈ E k) : H y ≤ z := by
    obtain ⟨q, hq, rfl⟩ := hy
    have hq' : q ∈ ⋃ k : Fin 2, Es k := mem_iUnion.mpr ⟨k, hq⟩
    rw [← hsub] at hq'
    exact hq'
  have hEdis : Disjoint (E 0) (E 1) := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
    exact disjoint_left.mp hEsdis hp ((hji (hpy.trans hqy.symm)).symm ▸ hq)
  have hEio : Disjoint (E i) (E o) := by
    fin_cases i <;> fin_cases o
    · exact False.elim (hio rfl)
    · exact hEdis
    · exact hEdis.symm
    · exact False.elim (hio rfl)
  have hcapbelow (k : Fin 2) : ∀ q ∈ (D.cap (W.label k)).sourceCap, f q < z := by
    rintro q ⟨p, hp, rfl⟩
    let C := D.cap (W.label k)
    have hmp : (C.profile.model p).2 ≤ 0 := by
      change C.profile.vertical _ * (heightCoordinates (p : E3)).2 ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (C.profile.vertical_pos _).le hp
    have heq := hh k ((C.profile.model p).1, ell k + C.scale * (C.profile.model p).2)
      (hs k ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le p), mem_univ _⟩)
    rw [hold k p hp] at heq
    change f (C.sourceChart p) = ell k + C.scale * (C.profile.model p).2 at heq
    have hn := mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hmp
    linarith [hell k]
  have hElevel (k : Fin 2) : E k ∩ {y : E3 | H y = z} = rim k := by
    ext y
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hqz⟩
      rcases hq with hq | ⟨p, hp, rfl⟩
      · exact False.elim ((ne_of_lt (hcapbelow k q hq)) hqz)
      · have hpz : p.2 = z := (W.leg_height k p (hlegsource k hp)).symm.trans hqz
        change j (W.leg k p) ∈ T k '' (sphere 0 1 ×ˢ ({z} : Set ℝ))
        rw [hcircle k z ⟨(hell k).le, by linarith [hgamma k]⟩]
        exact ⟨p.1, congrArg (fun t => j (W.leg k (p.1, t))) hpz.symm⟩
    · intro hy
      have hy' := hy
      change y ∈ T k '' (sphere 0 1 ×ˢ ({z} : Set ℝ)) at hy'
      rw [hcircle k z ⟨(hell k).le, by linarith [hgamma k]⟩] at hy'
      obtain ⟨q, rfl⟩ := hy'
      refine ⟨⟨W.leg k (q, z), Or.inr
        ⟨(q, z), ⟨mem_univ _, (hell k).le, le_rfl⟩, rfl⟩, rfl⟩, ?_⟩
      exact W.leg_height k (q, z) (hlegsource k ⟨mem_univ _, (hell k).le, le_rfl⟩)
  have hRimE (k : Fin 2) : rim k ⊆ E k := fun _ hy => ((hElevel k).symm ▸ hy).1
  have hRimH (k : Fin 2) (y : E3) (hy : y ∈ rim k) : H y = z :=
    ((hElevel k).symm ▸ hy).2
  have hRimD : rim i ⊆ Dtop :=
    image_mono (prod_mono sphere_subset_closedBall subset_rfl)
  have hDcompact : IsCompact Dtop :=
    ((isCompact_closedBall (0 : E2) 1).prod isCompact_singleton).image_of_continuousOn
      ((hT i).continuousOn.mono (fun _ hp => hs i ⟨hp.1, mem_univ _⟩))
  have hRcompact : IsCompact (rim o) :=
    ((isCompact_sphere (0 : E2) 1).prod isCompact_singleton).image_of_continuousOn
      ((hT o).continuousOn.mono (fun _ hp => hs o
        ⟨sphere_subset_closedBall hp.1, mem_univ _⟩))
  have hRimdisc : rim o =
      (fun x : E2 => (heightPlaneCoordinates u).symm (x, z)) '' (W.disc o).boundary := by
    change T o '' (sphere 0 1 ×ˢ ({z} : Set ℝ)) = _
    rw [hcircle o z ⟨(hell o).le, by linarith [hgamma o]⟩]
    exact (W.disc_boundary o).symm
  have hDdis : Disjoint Dtop (rim o) := by
    change Disjoint (T i '' _) (rim o)
    rw [hdisc i, hRimdisc]
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
    have heq := (heightPlaneCoordinates u).symm.injective (hpy.trans hqy.symm)
    have hpq : p = q := congrArg Prod.fst heq
    subst q
    exact disjoint_left.mp (W.disc o).inside_disjoint_boundary (hnested hp) hq
  let U := (W.leg 0).target ∪ (W.leg 1).target
  have hU : IsOpen U := (W.leg 0).open_target.union (W.leg 1).open_target
  have hlevelU (q : UnitTwoSphere) (hq : f q = z) : q ∈ U := by
    have hqs : q ∈ ⋃ k : Fin 2, Es k := hsub ▸ hq.le
    obtain ⟨k, hk⟩ := mem_iUnion.mp hqs
    rcases hk with hk | ⟨p, hp, rfl⟩
    · exact False.elim ((ne_of_lt (hcapbelow k q hk)) hq)
    · have ht := (W.leg k).map_source (hlegsource k hp)
      fin_cases k
      · exact Or.inl ht
      · exact Or.inr ht
  have hKU : IsCompact Uᶜ := isCompact_univ.of_isClosed_subset hU.isClosed_compl (subset_univ _)
  have hzU : z ∈ (f '' Uᶜ)ᶜ := by
    rintro ⟨q, hq, hqz⟩
    exact hq (hlevelU q hqz)
  obtain ⟨ds, hds, hdsball⟩ := Metric.isOpen_iff.mp
    (hKU.image hf).isClosed.isOpen_compl z hzU
  have hnearU (q : UnitTwoSphere) (hq : |f q - z| < ds) : q ∈ U := by
    by_contra hqu
    exact hdsball (by simpa only [mem_ball, Real.dist_eq] using hq) ⟨q, hqu, rfl⟩
  obtain ⟨Vi, Vo, hVi, hVo, hDVi, hRVo, hVdis⟩ :=
    SeparatedNhds.of_isCompact_isCompact hDcompact hRcompact hDdis
  have hexpand (k : Fin 2) (K : Set E2) (hK : IsCompact K)
      (hKball : K ⊆ closedBall 0 1) (V : Set E3) (hV : IsOpen V)
      (hKV : T k '' (K ×ˢ ({z} : Set ℝ)) ⊆ V) :
      ∃ e : ℝ, 0 < e ∧ ∀ p ∈ K ×ˢ Icc (z - e) (z + e), T k p ∈ V := by
    let O := (T k).source ∩ (T k) ⁻¹' V
    have hO : IsOpen O := (T k).isOpen_inter_preimage hV
    have hsubO : K ×ˢ ({z} : Set ℝ) ⊆ O := by
      intro p hp
      exact ⟨hs k ⟨hKball hp.1, mem_univ _⟩, hKV ⟨p, hp, rfl⟩⟩
    obtain ⟨X, J, hX, hJ, hDX, hzJ, hXJ⟩ :=
      generalized_tube_lemma hK isCompact_singleton hO hsubO
    obtain ⟨e, he, heJ⟩ := Metric.isOpen_iff.mp hJ z (hzJ (mem_singleton z))
    refine ⟨e / 2, by positivity, ?_⟩
    intro p hp
    apply (hXJ ⟨hDX hp.1, heJ ?_⟩).2
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hp.2.1, hp.2.2]
  obtain ⟨ei, hei, hbufferi⟩ := hexpand i (closedBall 0 1)
    (isCompact_closedBall _ _) subset_rfl Vi hVi hDVi
  obtain ⟨eo, heo, hbuffero⟩ := hexpand o (sphere 0 1)
    (isCompact_sphere _ _) sphere_subset_closedBall Vo hVo hRVo
  let b : Fin 2 → ℝ := fun k => min (z - ell k) (gamma k)
  have hb (k : Fin 2) : 0 < b k := lt_min (sub_pos.mpr (hell k)) (hgamma k)
  let m := min tau (min ds (min (min (b 0) (b 1)) (min ei eo)))
  have hm : 0 < m := lt_min htau (lt_min hds
    (lt_min (lt_min (hb 0) (hb 1)) (lt_min hei heo)))
  let d := m / 8
  have hd : 0 < d := by dsimp [d]; positivity
  have hd4 : 4 * d < m := by dsimp [d]; linarith
  have hdtau : 4 * d < tau := hd4.trans_le (min_le_left _ _)
  have hds' : 4 * d < ds := hd4.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdb (k : Fin 2) : 4 * d < b k := by
    apply hd4.trans_le
    have hm' : m ≤ min (b 0) (b 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    fin_cases k
    · exact hm'.trans (min_le_left _ _)
    · exact hm'.trans (min_le_right _ _)
  have hdel (k : Fin 2) : 4 * d < z - ell k := (hdb k).trans_le (min_le_left _ _)
  have hdg (k : Fin 2) : 4 * d < gamma k := (hdb k).trans_le (min_le_right _ _)
  have hde : 4 * d < min ei eo := hd4.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Z := Icc (z - 4 * d) (z + 4 * d)
  have hTbandi : T i '' (closedBall (0 : E2) 1 ×ˢ Z) ⊆ Vi := by
    rintro y ⟨p, hp, rfl⟩
    apply hbufferi p
    refine ⟨hp.1, ?_, ?_⟩ <;> linarith [hp.2.1, hp.2.2, hde.trans_le (min_le_left ei eo)]
  have hTbando : T o '' (sphere (0 : E2) 1 ×ˢ Z) ⊆ Vo := by
    rintro y ⟨p, hp, rfl⟩
    apply hbuffero p
    refine ⟨hp.1, ?_, ?_⟩ <;> linarith [hp.2.1, hp.2.2, hde.trans_le (min_le_right ei eo)]
  have htrack (k : Fin 2) (t : ℝ) (ht : t ∈ Z) : t ∈ Icc (ell k) (z + gamma k) := by
    constructor <;> linarith [ht.1, ht.2, hdel k, hdg k]
  have hSband (t : ℝ) (ht : t ∈ Z) : S ∩ {y : E3 | H y = t} =
      ⋃ k : Fin 2, T k '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨q, rfl⟩, hqt⟩
      have hqU : q ∈ U := hnearU q (by
        change |H (j q) - z| < ds
        rw [hqt, abs_lt]
        constructor <;> linarith [ht.1, ht.2, hds'])
      have hget (k : Fin 2) (hq : q ∈ (W.leg k).target) :
          j q ∈ T k '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) := by
        let p := (W.leg k).symm q
        have hp := (W.leg k).map_target hq
        have hph := W.leg_height k p hp
        rw [(W.leg k).right_inv hq] at hph
        have hpt : p.2 = t := hph.symm.trans hqt
        rw [hcircle k t (htrack k t ht)]
        refine ⟨p.1, ?_⟩
        change j (W.leg k (p.1, t)) = j q
        rw [← hpt]
        exact congrArg j ((W.leg k).right_inv hq)
      rcases hqU with hq | hq
      · exact mem_iUnion.mpr ⟨0, hget 0 hq⟩
      · exact mem_iUnion.mpr ⟨1, hget 1 hq⟩
    · intro hy
      obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      have hk' := hk
      rw [hcircle k t (htrack k t ht)] at hk'
      obtain ⟨q, hqy⟩ := hk'
      refine ⟨⟨W.leg k (q, t), hqy⟩, ?_⟩
      obtain ⟨p, hp, rfl⟩ := hk
      exact (hh k p (hs k ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)).trans hp.2
  refine ⟨d, hd, by linarith, by linarith [hdel i], ?_⟩
  intro lambda hlam hlamd
  let north : Set E3 :=
    (fun q : UnitTwoSphere => T i ((P.model q).1, z + lambda * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let C := D.cap (W.label i)
  obtain ⟨Q, A, ov, hov, hov1, hchart, hsource, htarget, hpoint, hinv,
    hbA, hAi, hAc, hcuts, hpatch⟩ := exists_two_profile_end_ball C.profile P u
      (T i) (hs i) (hT i) (hTi i) (hh i) (ell i) z C.scale lambda
      (hell i) C.scale_pos hlam
  have hAb : A.boundary = E i ∪ north := by
    have hcap : (fun q : UnitTwoSphere =>
        T i ((C.profile.model q).1, ell i + C.scale * (C.profile.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} = j '' C.sourceCap := by
      rw [SurgeryCapTag.sourceCap, image_image]
      exact image_congr (fun q hq => hold i q hq)
    have hleg : T i '' (sphere (0 : E2) 1 ×ˢ Icc (ell i) z) = j '' Lg i := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hslice : T i p ∈ T i '' (sphere 0 1 ×ˢ ({p.2} : Set ℝ)) :=
          ⟨p, ⟨hp.1, rfl⟩, rfl⟩
        rw [hcircle i p.2 ⟨hp.2.1, hp.2.2.trans (by linarith [hgamma i])⟩] at hslice
        obtain ⟨q, hq⟩ := hslice
        exact ⟨W.leg i (q, p.2), ⟨(q, p.2), ⟨mem_univ _, hp.2⟩, rfl⟩, hq⟩
      · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
        have hslice : j (W.leg i p) ∈ T i '' (sphere 0 1 ×ˢ ({p.2} : Set ℝ)) := by
          rw [hcircle i p.2 ⟨hp.2.1, hp.2.2.trans (by linarith [hgamma i])⟩]
          exact ⟨p.1, rfl⟩
        obtain ⟨r, hr, heq⟩ := hslice
        exact ⟨r, ⟨hr.1, hr.2.symm ▸ hp.2⟩, heq⟩
    have hn : (fun y : E3 => T i
        ((flatCapDiffeomorph P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
          (fun t => (P.horizontal_pos t).ne') (fun x => (P.vertical_pos x).ne')
            (heightCoordinates y)).1,
          z + lambda * (flatCapDiffeomorph P.horizontal P.vertical
            P.horizontal_smooth P.vertical_smooth (fun t => (P.horizontal_pos t).ne')
              (fun x => (P.vertical_pos x).ne') (heightCoordinates y)).2)) ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} = north := by
      ext y
      constructor
      · rintro ⟨q, ⟨hqn, hqh⟩, rfl⟩
        exact ⟨⟨q, mem_sphere_zero_iff_norm.mpr hqn⟩, hqh, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, rfl⟩
    rw [hbA, hcap, hleg, hn]
    change (j '' C.sourceCap ∪ j '' Lg i) ∪ north = j '' (C.sourceCap ∪ Lg i) ∪ north
    rw [image_union]
  have hcutTop : A.closedRegion ∩ {y : E3 | H y = z} = Dtop :=
    (hcuts z ⟨(hell i).le, le_rfl⟩).2
  have hAupper (y : E3) (hy : y ∈ A.closedRegion) : H y ≤ z + lambda * P.heightBound := by
    obtain ⟨p, hp, rfl⟩ := hAc hy
    rw [hh i p (hs i ⟨hp.1, mem_univ _⟩)]
    exact hp.2.2
  have hNh (y : E3) (hy : y ∈ north) : z ≤ H y := by
    obtain ⟨q, hq, rfl⟩ := hy
    change z ≤ H (T i ((P.model q).1, z + lambda * (P.model q).2))
    rw [hh i ((P.model q).1, z + lambda * (P.model q).2)
      (hs i ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩)]
    have hmP : 0 ≤ (P.model q).2 := by
      change 0 ≤ P.vertical _ * (heightCoordinates (q : E3)).2
      exact mul_nonneg (P.vertical_pos _).le hq
    exact le_add_of_nonneg_right (mul_nonneg hlam.le hmP)
  have hequator (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 = 0) :
      P.model q = ((heightCoordinates (q : E3)).1, 0) ∧
      ‖(heightCoordinates (q : E3)).1‖ = 1 := by
    have ha : P.horizontal 0 = 1 := by simpa using P.horizontal_near 0 (by norm_num)
    refine ⟨?_, ?_⟩
    · change flatCapDiffeomorph _ _ _ _ _ _ (heightCoordinates (q : E3)) = _
      rw [flatCapDiffeomorph_apply, hq, ha, one_smul, mul_zero]
    · have hn := heightCoordinates_norm_sq (q : E3)
      rw [norm_eq_of_mem_sphere q, hq] at hn
      nlinarith [norm_nonneg (heightCoordinates (q : E3)).1]
  have hNlevel : north ∩ {y : E3 | H y = z} = rim i := by
    ext y
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hzq⟩
      change H (T i ((P.model q).1, z + lambda * (P.model q).2)) = z at hzq
      rw [hh i ((P.model q).1, z + lambda * (P.model q).2)
        (hs i ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩)] at hzq
      have hmP : (P.model q).2 = 0 :=
        (mul_eq_zero.mp (show lambda * (P.model q).2 = 0 by
          linarith only [hzq])).resolve_left hlam.ne'
      have hqz : (heightCoordinates (q : E3)).2 = 0 := by
        change P.vertical _ * (heightCoordinates (q : E3)).2 = 0 at hmP
        exact (mul_eq_zero.mp hmP).resolve_left (P.vertical_pos _).ne'
      obtain ⟨hqmodel, hqn⟩ := hequator q hqz
      refine ⟨((heightCoordinates (q : E3)).1, z),
        ⟨mem_sphere_zero_iff_norm.mpr hqn, rfl⟩, ?_⟩
      change T i ((heightCoordinates (q : E3)).1, z) =
        T i ((P.model q).1, z + lambda * (P.model q).2)
      rw [hqmodel]
      simp only [mul_zero, add_zero]
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht' : t = z := ht
      subst t
      have hx' : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hqn : ‖heightCoordinates.symm (x, (0 : ℝ))‖ = 1 := by
        have hn := heightCoordinates_symm_norm_sq (x, (0 : ℝ))
        rw [hx'] at hn
        nlinarith [norm_nonneg (heightCoordinates.symm (x, (0 : ℝ)))]
      let q : UnitTwoSphere := ⟨heightCoordinates.symm (x, 0), mem_sphere_zero_iff_norm.mpr hqn⟩
      have hqh : (heightCoordinates (q : E3)).2 = 0 := by
        change (heightCoordinates (heightCoordinates.symm (x, 0))).2 = 0
        rw [heightCoordinates.apply_symm_apply]
      have hqm : P.model q = (x, 0) := by
        simpa only [q, heightCoordinates.apply_symm_apply] using (hequator q hqh).1
      refine ⟨⟨q, hqh.ge, ?_⟩, hh i _ (hs i ⟨sphere_subset_closedBall hx, mem_univ _⟩)⟩
      change T i ((P.model q).1, z + lambda * (P.model q).2) = T i (x, z)
      rw [hqm]
      simp only [mul_zero, add_zero]
  have hRimN : rim i ⊆ north := fun _ hy => (hNlevel.symm ▸ hy).1
  have hEN : E i ∩ north = rim i := by
    ext y
    constructor
    · intro hy
      rw [← hNlevel]
      exact ⟨hy.2, le_antisymm (hEh i y hy.1) (hNh y hy.2)⟩
    · intro hy
      exact ⟨hRimE i hy, hRimN hy⟩
  have houterBoundary : Disjoint (E o) A.boundary := by
    rw [hAb]
    apply disjoint_left.mpr
    rintro y hyO (hyI | hyN)
    · exact disjoint_left.mp hEio hyI hyO
    · have hyz : H y = z := le_antisymm (hEh o y hyO) (hNh y hyN)
      exact disjoint_left.mp hDdis
        (hRimD (hNlevel.subset ⟨hyN, hyz⟩)) ((hElevel o).subset ⟨hyO, hyz⟩)
  have hRimOutside : rim o ⊆ A.closedRegionᶜ := by
    intro y hy hyA
    exact disjoint_left.mp hDdis (hcutTop ▸ ⟨hyA, hRimH o y hy⟩) hy
  let q0 : UnitCircle := circleDirection (0 : E2)
  have hRimNonempty : (rim o).Nonempty :=
    ⟨T o ((q0 : E2), z), ((q0 : E2), z), ⟨q0.property, rfl⟩, rfl⟩
  have hEconnected : IsConnected (E o) := (hEs o).2.image j hj.continuousOn
  have hEoutside : E o ⊆ A.closedRegionᶜ := by
    rcases A.preconnected_subset_inside_or_outside
      hEconnected.isPreconnected houterBoundary with hin | hout
    · obtain ⟨y, hy⟩ := hRimNonempty
      apply False.elim
      apply hRimOutside hy
      rw [← A.inside_union_boundary]
      exact Or.inl (hin (hRimE o hy))
    · exact hout
  have hAouter : Disjoint A.closedRegion (E o) := by
    exact disjoint_left.mpr (fun _ hyA hyE => hEoutside hyE hyA)
  have hinsideS : Disjoint A.inside S := by
    apply disjoint_left.mpr
    intro y hyi hyS
    have hyA : y ∈ A.closedRegion := by
      rw [← A.inside_union_boundary]
      exact Or.inl hyi
    by_cases hyz : H y ≤ z
    · obtain ⟨q, rfl⟩ := hyS
      have hq : q ∈ ⋃ k : Fin 2, Es k := hsub ▸ hyz
      obtain ⟨k, hqk⟩ := mem_iUnion.mp hq
      have hyE : j q ∈ E k := ⟨q, hqk, rfl⟩
      by_cases hki : k = i
      · subst k
        exact disjoint_left.mp A.inside_disjoint_boundary hyi (hAb.symm ▸ Or.inl hyE)
      · have hko : k = o := by omega
        exact hEoutside (hko ▸ hyE) hyA
    · have hyz' : z < H y := lt_of_not_ge hyz
      have hyZ : H y ∈ Z := by
        have hu := hAupper y hyA
        constructor <;> linarith
      have hycircles : y ∈ ⋃ k : Fin 2, T k '' (sphere 0 1 ×ˢ ({H y} : Set ℝ)) :=
        hSband (H y) hyZ ▸ ⟨hyS, rfl⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hycircles
      obtain ⟨p, hp, hpy⟩ := hAi hyi
      have hps := hs i ⟨ball_subset_closedBall hp.1, mem_univ _⟩
      have hph : p.2 = H y := (hh i p hps).symm.trans (congrArg H hpy)
      by_cases hki : k = i
      · subst k
        obtain ⟨r, hr, hry⟩ := hk
        have heq := (T i).injOn hps
          (hs i ⟨sphere_subset_closedBall hr.1, mem_univ _⟩) (hpy.trans hry.symm)
        have hnorm : ‖p.1‖ = 1 := by
          rw [congrArg Prod.fst heq]
          exact mem_sphere_zero_iff_norm.mp hr.1
        exact (ne_of_lt (mem_ball_zero_iff.mp hp.1)) hnorm
      · have hko : k = o := by omega
        subst k
        have hyVi : y ∈ Vi := hTbandi ⟨p,
          ⟨ball_subset_closedBall hp.1, hph.symm ▸ hyZ⟩, hpy⟩
        have hyVo : y ∈ Vo := by
          obtain ⟨r, hr, hry⟩ := hk
          exact hTbando ⟨r, ⟨hr.1, hr.2.symm ▸ hyZ⟩, hry⟩
        exact disjoint_left.mp hVdis hyVi hyVo
  have hret : A.closedRegion ∩ (R ∪ E o) ⊆ north := by
    rintro y ⟨hyA, hyRet⟩
    have hyS : y ∈ S := hyRet.elim (fun h => h.1) (fun h => hES o h)
    have hyB : y ∈ A.boundary := by
      rw [← A.inside_union_boundary] at hyA
      exact hyA.resolve_left (fun h => disjoint_left.mp hinsideS h hyS)
    rw [hAb] at hyB
    rcases hyB with hyE | hyN
    · rcases hyRet with hyR | hyOther
      · have hyz : H y = z := le_antisymm (hEh i y hyE) hyR.2
        exact hRimN (hElevel i ▸ ⟨hyE, hyz⟩)
      · exact False.elim (disjoint_left.mp hEio hyE hyOther)
    · exact hyN
  exact ⟨Q, A, ov, hov, hov1, hchart, hsource, htarget, hpoint, hinv,
    hAb, hAi, hAc, hcuts, hpatch, hinsideS, hAouter, hret, hEN⟩

end PoincareConjecture.M25.Topology3D
