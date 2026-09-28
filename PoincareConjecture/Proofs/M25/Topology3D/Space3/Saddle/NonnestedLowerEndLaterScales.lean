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



theorem exists_saddle_nonnested_lower_end_later_scales
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (P : SurgeryCapProfile) (tau : ℝ) (htau : 0 < tau) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let L := heightPlaneCoordinates u
    let S : Set E3 := range j
    let R : Set E3 := S ∩ {y : E3 | W.level ≤ H y}
    let C := fun i : Fin 2 => D.cap (W.label i)
    let ell : Fin 2 → ℝ := fun i => (C i).cutHeight + (C i).removal
    let E : Fin 2 → Set E3 := fun i => j ''
      ((C i).sourceCap ∪ W.leg i '' (univ ×ˢ Icc (ell i) W.level))
    ∃ (r gamma ov w : Fin 2 → ℝ)
      (T : Fin 2 → OpenPartialHomeomorph (E2 × ℝ) E3)
      (phase : Fin 2 → ℝ → Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞)
      (d : ℝ) (V : Fin 2 → Set E3),
      (∀ i : Fin 2,
        1 < r i ∧ 0 < gamma i ∧ gamma i < (W.level - ell i) / 8 ∧
        0 < ov i ∧ ov i ≤ (C i).overlapWidth ∧ (C i).scale * ov i < gamma i / 2 ∧
        0 < w i ∧ w i ≤ (C i).collarWidth ∧ |(C i).beta| * w i < (C i).scale / 2 ∧
        (T i).source =
          ((C i).tube.source ∩ (ball (0 : E2) (r i) ×ˢ Iio (ell i + gamma i))) ∪
            (ball (0 : E2) (r i) ×ˢ Ioi (ell i - gamma i)) ∧
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
        ContDiffOn ℝ ∞ (T i) (T i).source ∧
        ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
        (∀ p ∈ (T i).source, H (T i p) = p.2) ∧
        (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) ∧
        (∀ p ∈ (C i).tube.source,
          ‖p.1‖ < r i → p.2 < ell i + gamma i → T i p = (C i).tube p) ∧
        (∀ p ∈ (C i).tube.source,
          ‖p.1‖ < r i → p.2 < ell i + gamma i →
            (C i).tube p ∈ (T i).target ∧ (T i).symm ((C i).tube p) = p) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
          (fun p : ℝ × UnitCircle => phase i p.1 p.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
          (fun p : ℝ × UnitCircle => (phase i p.1).symm p.2) ∧
        (∀ z ∈ Icc (ell i) (W.level + gamma i), ∀ q : UnitCircle,
          (phase i z q, z) ∈ (W.leg i).source ∧
          T i (q.1, z) = j (W.leg i (phase i z q, z))) ∧
        (∀ z ∈ Icc (ell i) (W.level + gamma i),
          T i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
            range (fun q : UnitCircle => j (W.leg i (q, z)))) ∧
        T i '' (ball (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
          (fun x : E2 => L.symm (x, W.level)) '' (W.disc i).inside ∧
        T i '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
          (fun x : E2 => L.symm (x, W.level)) '' (W.disc i).closedRegion ∧
        (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < ov i →
          psi ((C i).sourceChart q, 0) =
            (C i).profile.capMap (T i) (C i).cutHeight (C i).sign
              (C i).removal (C i).scale q) ∧
        (C i).cap = (C i).profile.capMap (T i) (C i).cutHeight (C i).sign
          (C i).removal (C i).scale ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
        (∀ x : E2, ‖x‖ ≤ 1 / 8 → ∀ s : ℝ, |s| < w i →
          psi ((C i).flatChart x, s) = T i
            (x, (C i).cutHeight + (C i).sign * ((C i).removal - (C i).scale) +
              (C i).beta * s))) ∧
      0 < d ∧ 4 * d < tau ∧
      (∀ i : Fin 2,
        4 * d < W.level - ell i ∧ 4 * d < gamma i ∧ IsOpen (V i) ∧
        T i '' (closedBall (0 : E2) 1 ×ˢ Icc (W.level - 4 * d) (W.level + 4 * d)) ⊆
          V i) ∧
      Disjoint (V 0) (V 1) ∧
      (∀ t ∈ Icc (W.level - 4 * d) (W.level + 4 * d),
        S ∩ {y : E3 | H y = t} =
          ⋃ i : Fin 2, T i '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ))) ∧
      S = R ∪ E 0 ∪ E 1 ∧ IsCompact R ∧
      ∀ (lambda : Fin 2 → ℝ),
        (∀ i : Fin 2, 0 < lambda i) →
        (∀ i : Fin 2, lambda i * P.heightBound < d) →
        ∃ (Q : Fin 2 → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
          (A : Fin 2 → BallNeighborhoodChart E3 E3) (o : Fin 2 → ℝ),
          let north : Fin 2 → Set E3 := fun i =>
            (fun q : UnitTwoSphere => T i
              ((P.model q).1, W.level + lambda i * (P.model q).2)) ''
                {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
          let rim : Fin 2 → Set E3 := fun i =>
            T i '' (sphere (0 : E2) 1 ×ˢ ({W.level} : Set ℝ))
          let other : Fin 2 → Fin 2 := ![1, 0]
          (∀ i : Fin 2,
            0 < o i ∧ o i < 1 / 4 ∧ lambda i * P.heightBound < tau ∧
            lambda i * P.heightBound < W.level - ell i ∧
            (A i).chart = (Q i).toHomeomorph.toOpenPartialHomeomorph.trans (T i) ∧
            (A i).chart.source = (Q i) ⁻¹' (T i).source ∧
            (A i).chart.target = (T i).target ∧
            (∀ y : E3, (A i).chart y = T i (Q i y)) ∧
            (∀ y : E3, (A i).chart.symm y = (Q i).symm ((T i).symm y)) ∧
            (A i).boundary = E i ∪ north i ∧
            (A i).inside ⊆ T i '' (ball (0 : E2) 1 ×ˢ (univ : Set ℝ)) ∧
            (A i).closedRegion ⊆ T i '' (closedBall (0 : E2) 1 ×ˢ
              Icc (ell i - (C i).scale * (C i).profile.heightBound)
                (W.level + lambda i * P.heightBound)) ∧
            (∀ y ∈ (A i).closedRegion, H y ≤ W.level + lambda i * P.heightBound) ∧
            (∀ t ∈ Icc (ell i) W.level,
              (A i).inside ∩ {y : E3 | H y = t} =
                T i '' (ball (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ∧
              (A i).closedRegion ∩ {y : E3 | H y = t} =
                T i '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ))) ∧
            (A i).closedRegion ∩ {y : E3 | H y = W.level} =
              (fun x : E2 => L.symm (x, W.level)) '' (W.disc i).closedRegion ∧
            (∀ q : UnitTwoSphere, -o i < (heightCoordinates (q : E3)).2 →
              T i ((P.model q).1, W.level + lambda i * (P.model q).2) ∈
                (A i).boundary) ∧
            Disjoint (A i).inside S ∧
            (A i).closedRegion ∩ (R ∪ E (other i)) ⊆ north i ∧
            E i ∩ north i = rim i) ∧
          Disjoint (A 0).closedRegion (A 1).closedRegion := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let f : UnitTwoSphere → ℝ := fun q => H (j q)
  let z := W.level
  let S : Set E3 := range j
  let R : Set E3 := S ∩ {y : E3 | z ≤ H y}
  let ell : Fin 2 → ℝ := fun i =>
    (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal
  let Lg : Fin 2 → Set UnitTwoSphere := fun i =>
    W.leg i '' (univ ×ˢ Icc (ell i) z)
  let Es : Fin 2 → Set UnitTwoSphere := fun i => (D.cap (W.label i)).sourceCap ∪ Lg i
  let E : Fin 2 → Set E3 := fun i => j '' Es i
  let other : Fin 2 → Fin 2 := ![1, 0]
  have hoo (i : Fin 2) : other (other i) = i := by fin_cases i <;> rfl
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  have hf : Continuous f := H.continuous.comp hj
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      (show (p, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 by norm_num)
      (show (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1 : ℝ) 1 by norm_num) hpq)
  obtain ⟨hlabels, hsub, hEs, hEsdis⟩ :=
    SaddleLowerLevelData.source_sublevel_decomposition psi hpsi u D W
  change {q : UnitTwoSphere | f q ≤ z} = ⋃ i : Fin 2, Es i at hsub
  change Disjoint (Es 0) (Es 1) at hEsdis
  have hell (i : Fin 2) : ell i < z := by
    simpa only [ell, W.label_lower i, one_mul] using
      W.lower_seams_lt_level (W.label i) (W.label_lower i)
  have hlegsource (i : Fin 2) : univ ×ˢ Icc (ell i) z ⊆ (W.leg i).source := by
    simpa only [ell, W.label_lower i, one_mul] using W.leg_source i
  have hES (i : Fin 2) : E i ⊆ S := by
    rintro y ⟨q, _, rfl⟩
    exact mem_range_self q
  have hEh (i : Fin 2) (y : E3) (hy : y ∈ E i) : H y ≤ z := by
    obtain ⟨q, hq, rfl⟩ := hy
    have hq' : q ∈ ⋃ k : Fin 2, Es k := mem_iUnion.mpr ⟨i, hq⟩
    rw [← hsub] at hq'
    exact hq'
  have hEdis : Disjoint (E 0) (E 1) := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
    exact disjoint_left.mp hEsdis hp ((hji (hpy.trans hqy.symm)).symm ▸ hq)
  have hEdisother (i : Fin 2) : Disjoint (E i) (E (other i)) := by
    fin_cases i
    · exact hEdis
    · exact hEdis.symm
  have htube (i : Fin 2) := exists_saddle_lower_end_tube hP psi hpsi u D W i
  choose r gamma ov w T phase hr hgamma hgap hov hovold hovg hw hwold hwb
    hseq hs hT hTi hh hhi htold htoldi hphase hphasei hphasepoint
    hcircle hopen hdisc hcentral hcap hflat using htube
  have hold (i : Fin 2) (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      T i (((D.cap (W.label i)).profile.model q).1,
        ell i + (D.cap (W.label i)).scale * ((D.cap (W.label i)).profile.model q).2) =
          j ((D.cap (W.label i)).sourceChart q) := by
    have heq := (hcentral i q (lt_of_le_of_lt hq (hov i))).symm
    simpa only [SurgeryCapProfile.capMap_apply, W.label_lower i, one_mul,
      ell, add_assoc] using heq
  let rim : Fin 2 → Set E3 := fun i => T i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))
  let Dtop : Fin 2 → Set E3 := fun i => T i '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))
  have hcapbelow (i : Fin 2) : ∀ q ∈ (D.cap (W.label i)).sourceCap, f q < z := by
    rintro q ⟨p, hp, rfl⟩
    let C := D.cap (W.label i)
    have hmp : (C.profile.model p).2 ≤ 0 := by
      change C.profile.vertical _ * (heightCoordinates (p : E3)).2 ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (C.profile.vertical_pos _).le hp
    have heq := hh i ((C.profile.model p).1, ell i + C.scale * (C.profile.model p).2)
      (hs i ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le p), mem_univ _⟩)
    rw [hold i p hp] at heq
    change f (C.sourceChart p) = ell i + C.scale * (C.profile.model p).2 at heq
    have hn := mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hmp
    linarith [hell i]
  have hElevel (i : Fin 2) : E i ∩ {y : E3 | H y = z} = rim i := by
    ext y
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hqz⟩
      rcases hq with hq | ⟨p, hp, rfl⟩
      · exact False.elim ((ne_of_lt (hcapbelow i q hq)) hqz)
      · have hpz : p.2 = z := (W.leg_height i p (hlegsource i hp)).symm.trans hqz
        change j (W.leg i p) ∈ T i '' (sphere 0 1 ×ˢ ({z} : Set ℝ))
        rw [hcircle i z ⟨(hell i).le, by linarith [hgamma i]⟩]
        exact ⟨p.1, congrArg (fun t => j (W.leg i (p.1, t))) hpz.symm⟩
    · intro hy
      have hy' := hy
      change y ∈ T i '' (sphere 0 1 ×ˢ ({z} : Set ℝ)) at hy'
      rw [hcircle i z ⟨(hell i).le, by linarith [hgamma i]⟩] at hy'
      obtain ⟨q, rfl⟩ := hy'
      refine ⟨⟨W.leg i (q, z), Or.inr
        ⟨(q, z), ⟨mem_univ _, (hell i).le, le_rfl⟩, rfl⟩, rfl⟩, ?_⟩
      exact W.leg_height i (q, z) (hlegsource i ⟨mem_univ _, (hell i).le, le_rfl⟩)
  have hRimE (i : Fin 2) : rim i ⊆ E i := fun _ hy => ((hElevel i).symm ▸ hy).1
  have hRimH (i : Fin 2) (y : E3) (hy : y ∈ rim i) : H y = z :=
    ((hElevel i).symm ▸ hy).2
  have hRimD (i : Fin 2) : rim i ⊆ Dtop i :=
    image_mono (prod_mono sphere_subset_closedBall subset_rfl)
  have hDcompact (i : Fin 2) : IsCompact (Dtop i) :=
    ((isCompact_closedBall (0 : E2) 1).prod isCompact_singleton).image_of_continuousOn
      ((hT i).continuousOn.mono (fun _ hp => hs i ⟨hp.1, mem_univ _⟩))
  have hDdis : Disjoint (Dtop 0) (Dtop 1) := by
    change Disjoint (T 0 '' _) (T 1 '' _)
    rw [hdisc 0, hdisc 1]
    apply disjoint_left.mpr
    rintro y ⟨p, hp, hpy⟩ ⟨q, hq, hqy⟩
    have heq := (heightPlaneCoordinates u).symm.injective (hpy.trans hqy.symm)
    have hpq : p = q := congrArg Prod.fst heq
    subst q
    exact disjoint_left.mp hnonnested hp hq
  have hDdisother (i : Fin 2) : Disjoint (Dtop i) (Dtop (other i)) := by
    fin_cases i
    · exact hDdis
    · exact hDdis.symm
  let U := (W.leg 0).target ∪ (W.leg 1).target
  have hU : IsOpen U := (W.leg 0).open_target.union (W.leg 1).open_target
  have hlevelU (q : UnitTwoSphere) (hq : f q = z) : q ∈ U := by
    have hqs : q ∈ ⋃ i : Fin 2, Es i := hsub ▸ hq.le
    obtain ⟨i, hi⟩ := mem_iUnion.mp hqs
    rcases hi with hi | ⟨p, hp, rfl⟩
    · exact False.elim ((ne_of_lt (hcapbelow i q hi)) hq)
    · have ht := (W.leg i).map_source (hlegsource i hp)
      fin_cases i
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
  obtain ⟨V0, V1, hV0, hV1, hD0V, hD1V, hVdis⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hDcompact 0) (hDcompact 1) hDdis
  let V : Fin 2 → Set E3 := ![V0, V1]
  have hV (i : Fin 2) : IsOpen (V i) := by fin_cases i <;> assumption
  have hDV (i : Fin 2) : Dtop i ⊆ V i := by fin_cases i <;> assumption
  have hVdisother (i : Fin 2) : Disjoint (V i) (V (other i)) := by
    fin_cases i
    · exact hVdis
    · exact hVdis.symm
  have hexpand (i : Fin 2) : ∃ e : ℝ, 0 < e ∧
      ∀ p ∈ closedBall (0 : E2) 1 ×ˢ Icc (z - e) (z + e), T i p ∈ V i := by
    let O := (T i).source ∩ (T i) ⁻¹' V i
    have hO : IsOpen O := (T i).isOpen_inter_preimage (hV i)
    have hsubO : closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) ⊆ O := by
      intro p hp
      exact ⟨hs i ⟨hp.1, mem_univ _⟩, hDV i ⟨p, hp, rfl⟩⟩
    obtain ⟨X, J, hX, hJ, hDX, hzJ, hXJ⟩ :=
      generalized_tube_lemma (isCompact_closedBall (0 : E2) 1) isCompact_singleton hO hsubO
    obtain ⟨e, he, heJ⟩ := Metric.isOpen_iff.mp hJ z (hzJ (mem_singleton z))
    refine ⟨e / 2, by positivity, ?_⟩
    intro p hp
    apply (hXJ ⟨hDX hp.1, heJ ?_⟩).2
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hp.2.1, hp.2.2]
  choose eps heps hbuffer using hexpand
  let b : Fin 2 → ℝ := fun i => min (z - ell i) (min (gamma i) (eps i))
  have hb (i : Fin 2) : 0 < b i := lt_min (sub_pos.mpr (hell i)) (lt_min (hgamma i) (heps i))
  let m := min tau (min ds (min (b 0) (b 1)))
  have hm : 0 < m := lt_min htau (lt_min hds (lt_min (hb 0) (hb 1)))
  let d := m / 8
  have hd : 0 < d := by dsimp [d]; positivity
  have hd4 : 4 * d < m := by dsimp [d]; linarith
  have hdtau : 4 * d < tau := hd4.trans_le (min_le_left _ _)
  have hds' : 4 * d < ds := hd4.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdb (i : Fin 2) : 4 * d < b i := by
    apply hd4.trans_le
    have hh : m ≤ min (b 0) (b 1) := (min_le_right _ _).trans (min_le_right _ _)
    fin_cases i
    · exact hh.trans (min_le_left _ _)
    · exact hh.trans (min_le_right _ _)
  have hdel (i : Fin 2) : 4 * d < z - ell i := (hdb i).trans_le (min_le_left _ _)
  have hdg (i : Fin 2) : 4 * d < gamma i :=
    (hdb i).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hde (i : Fin 2) : 4 * d < eps i :=
    (hdb i).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let Z := Icc (z - 4 * d) (z + 4 * d)
  have hTband (i : Fin 2) : T i '' (closedBall (0 : E2) 1 ×ˢ Z) ⊆ V i := by
    rintro y ⟨p, hp, rfl⟩
    apply hbuffer i p
    refine ⟨hp.1, ?_, ?_⟩ <;> linarith [hp.2.1, hp.2.2, hde i]
  have htrack (i : Fin 2) (t : ℝ) (ht : t ∈ Z) : t ∈ Icc (ell i) (z + gamma i) := by
    constructor <;> linarith [ht.1, ht.2, hdel i, hdg i]
  have hSband (t : ℝ) (ht : t ∈ Z) : S ∩ {y : E3 | H y = t} =
      ⋃ i : Fin 2, T i '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨q, rfl⟩, hqt⟩
      have hqU : q ∈ U := hnearU q (by
        change |H (j q) - z| < ds
        rw [hqt, abs_lt]
        constructor <;> linarith [ht.1, ht.2, hds'])
      have hget (i : Fin 2) (hq : q ∈ (W.leg i).target) :
          j q ∈ T i '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) := by
        let p := (W.leg i).symm q
        have hp := (W.leg i).map_target hq
        have hph := W.leg_height i p hp
        rw [(W.leg i).right_inv hq] at hph
        have hpt : p.2 = t := hph.symm.trans hqt
        rw [hcircle i t (htrack i t ht)]
        refine ⟨p.1, ?_⟩
        change j (W.leg i (p.1, t)) = j q
        rw [← hpt]
        exact congrArg j ((W.leg i).right_inv hq)
      rcases hqU with hq | hq
      · exact mem_iUnion.mpr ⟨0, hget 0 hq⟩
      · exact mem_iUnion.mpr ⟨1, hget 1 hq⟩
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      have hi' := hi
      rw [hcircle i t (htrack i t ht)] at hi'
      obtain ⟨q, hqy⟩ := hi'
      refine ⟨⟨W.leg i (q, t), hqy⟩, ?_⟩
      obtain ⟨p, hp, rfl⟩ := hi
      exact (hh i p (hs i ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)).trans hp.2
  have hSdecomp : S = R ∪ E 0 ∪ E 1 := by
    ext y
    constructor
    · intro hy
      by_cases hzy : z ≤ H y
      · exact Or.inl (Or.inl ⟨hy, hzy⟩)
      · obtain ⟨q, rfl⟩ := hy
        have hq : q ∈ ⋃ i : Fin 2, Es i := hsub ▸ (lt_of_not_ge hzy).le
        obtain ⟨i, hi⟩ := mem_iUnion.mp hq
        have hyE : j q ∈ E i := ⟨q, hi, rfl⟩
        fin_cases i
        · exact Or.inl (Or.inr hyE)
        · exact Or.inr hyE
    · rintro ((hy | hy) | hy)
      · exact hy.1
      · exact hES 0 hy
      · exact hES 1 hy
  have hR : IsCompact R :=
    (isCompact_range hj).inter_right (isClosed_le continuous_const H.continuous)
  refine ⟨r, gamma, ov, w, T, phase, d, V, ?_, hd, hdtau, ?_, hVdis,
    hSband, hSdecomp, hR, ?_⟩
  · intro i
    exact ⟨hr i, hgamma i, hgap i, hov i, hovold i, hovg i, hw i, hwold i, hwb i,
      hseq i, hs i, hT i, hTi i, hh i, hhi i, htold i, htoldi i, hphase i,
      hphasei i, hphasepoint i, hcircle i, hopen i, hdisc i, hcentral i, hcap i, hflat i⟩
  · intro i
    exact ⟨hdel i, hdg i, hV i, hTband i⟩
  intro lambda hlam hlamd
  let north : Fin 2 → Set E3 := fun i =>
    (fun q : UnitTwoSphere => T i ((P.model q).1, z + lambda i * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  have hballs (i : Fin 2) :
      ∃ (Q : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
        (A : BallNeighborhoodChart E3 E3) (o : ℝ),
      0 < o ∧ o < 1 / 4 ∧
      A.chart = Q.toHomeomorph.toOpenPartialHomeomorph.trans (T i) ∧
      A.chart.source = Q ⁻¹' (T i).source ∧ A.chart.target = (T i).target ∧
      (∀ y : E3, A.chart y = T i (Q y)) ∧
      (∀ y : E3, A.chart.symm y = Q.symm ((T i).symm y)) ∧
      A.boundary = E i ∪ north i ∧
      A.inside ⊆ T i '' (ball (0 : E2) 1 ×ˢ (univ : Set ℝ)) ∧
      A.closedRegion ⊆ T i '' (closedBall (0 : E2) 1 ×ˢ
        Icc (ell i - (D.cap (W.label i)).scale * (D.cap (W.label i)).profile.heightBound)
          (z + lambda i * P.heightBound)) ∧
      (∀ t ∈ Icc (ell i) z,
        A.inside ∩ {y : E3 | H y = t} = T i '' (ball (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ∧
        A.closedRegion ∩ {y : E3 | H y = t} =
          T i '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ))) ∧
      ∀ q : UnitTwoSphere, -o < (heightCoordinates (q : E3)).2 →
        T i ((P.model q).1, z + lambda i * (P.model q).2) ∈ A.boundary := by
    let C := D.cap (W.label i)
    obtain ⟨Q, A, o, ho, ho1, hchart, hsource, htarget, hpoint, hinv,
      hb, hi, hc, hcuts, hpatch⟩ := exists_two_profile_end_ball C.profile P u
        (T i) (hs i) (hT i) (hTi i) (hh i) (ell i) z C.scale (lambda i)
        (hell i) C.scale_pos (hlam i)
    refine ⟨Q, A, o, ho, ho1, hchart, hsource, htarget, hpoint, hinv, ?_, hi, hc,
      hcuts, hpatch⟩
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
          z + lambda i * (flatCapDiffeomorph P.horizontal P.vertical
            P.horizontal_smooth P.vertical_smooth (fun t => (P.horizontal_pos t).ne')
              (fun x => (P.vertical_pos x).ne') (heightCoordinates y)).2)) ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} = north i := by
      ext y
      constructor
      · rintro ⟨q, ⟨hqn, hqh⟩, rfl⟩
        exact ⟨⟨q, mem_sphere_zero_iff_norm.mpr hqn⟩, hqh, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, rfl⟩
    rw [hb, hcap, hleg, hn]
    change (j '' C.sourceCap ∪ j '' Lg i) ∪ north i = j '' (C.sourceCap ∪ Lg i) ∪ north i
    rw [image_union]
  choose Q A o ho ho1 hchart hsource htarget hpoint hinv hAb hAi hAc hcuts hpatch using hballs
  have hcut (i : Fin 2) (t : ℝ) (ht : t ∈ Icc (ell i) z) :
      (A i).closedRegion ∩ {y : E3 | H y = t} =
        T i '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) := (hcuts i t ht).2
  have hcutTop (i : Fin 2) : (A i).closedRegion ∩ {y : E3 | H y = z} = Dtop i :=
    hcut i z ⟨(hell i).le, le_rfl⟩
  have hAupper (i : Fin 2) (y : E3) (hy : y ∈ (A i).closedRegion) :
      H y ≤ z + lambda i * P.heightBound := by
    obtain ⟨p, hp, rfl⟩ := hAc i hy
    rw [hh i p (hs i ⟨hp.1, mem_univ _⟩)]
    exact hp.2.2
  have hNh (i : Fin 2) (y : E3) (hy : y ∈ north i) : z ≤ H y := by
    obtain ⟨q, hq, rfl⟩ := hy
    change z ≤ H (T i ((P.model q).1, z + lambda i * (P.model q).2))
    rw [hh i ((P.model q).1, z + lambda i * (P.model q).2)
      (hs i ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩)]
    have hm : 0 ≤ (P.model q).2 := by
      change 0 ≤ P.vertical _ * (heightCoordinates (q : E3)).2
      exact mul_nonneg (P.vertical_pos _).le hq
    exact le_add_of_nonneg_right (mul_nonneg (hlam i).le hm)
  have hNV (i : Fin 2) : north i ⊆ V i := by
    rintro y ⟨q, hq, rfl⟩
    apply hTband i
    refine ⟨((P.model q).1, z + lambda i * (P.model q).2),
      ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), ?_⟩, rfl⟩
    have hh' := mul_le_mul_of_nonneg_left (abs_le.mp (P.height_bound q)).1 (hlam i).le
    have hh'' := mul_le_mul_of_nonneg_left (abs_le.mp (P.height_bound q)).2 (hlam i).le
    change lambda i * -P.heightBound ≤ lambda i * (P.model q).2 at hh'
    change lambda i * (P.model q).2 ≤ lambda i * P.heightBound at hh''
    change z - 4 * d ≤ z + lambda i * (P.model q).2 ∧
      z + lambda i * (P.model q).2 ≤ z + 4 * d
    constructor <;> linarith [hlamd i]
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
  have hNlevel (i : Fin 2) : north i ∩ {y : E3 | H y = z} = rim i := by
    ext y
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hzq⟩
      change H (T i ((P.model q).1, z + lambda i * (P.model q).2)) = z at hzq
      rw [hh i ((P.model q).1, z + lambda i * (P.model q).2)
        (hs i ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩)] at hzq
      have hm : (P.model q).2 = 0 :=
        (mul_eq_zero.mp (show lambda i * (P.model q).2 = 0 by
          linarith only [hzq])).resolve_left (hlam i).ne'
      have hqz : (heightCoordinates (q : E3)).2 = 0 := by
        change P.vertical _ * (heightCoordinates (q : E3)).2 = 0 at hm
        exact (mul_eq_zero.mp hm).resolve_left (P.vertical_pos _).ne'
      obtain ⟨hqmodel, hqn⟩ := hequator q hqz
      refine ⟨((heightCoordinates (q : E3)).1, z),
        ⟨mem_sphere_zero_iff_norm.mpr hqn, rfl⟩, ?_⟩
      change T i ((heightCoordinates (q : E3)).1, z) =
        T i ((P.model q).1, z + lambda i * (P.model q).2)
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
      change T i ((P.model q).1, z + lambda i * (P.model q).2) = T i (x, z)
      rw [hqm]
      simp only [mul_zero, add_zero]
  have hRimN (i : Fin 2) : rim i ⊆ north i := fun _ hy => ((hNlevel i).symm ▸ hy).1
  have hEN (i : Fin 2) : E i ∩ north i = rim i := by
    ext y
    constructor
    · intro hy
      rw [← hNlevel i]
      exact ⟨hy.2, le_antisymm (hEh i y hy.1) (hNh i y hy.2)⟩
    · intro hy
      exact ⟨hRimE i hy, hRimN i hy⟩
  have hcross (i : Fin 2) : Disjoint (E i) (north (other i)) := by
    apply disjoint_left.mpr
    intro y hyE hyN
    have hyz : H y = z := le_antisymm (hEh i y hyE) (hNh (other i) y hyN)
    exact disjoint_left.mp (hDdisother i)
      (hRimD i ((hElevel i).subset ⟨hyE, hyz⟩))
      (hRimD (other i) ((hNlevel (other i)).subset ⟨hyN, hyz⟩))
  have hBdis (i : Fin 2) : Disjoint (A i).boundary (A (other i)).boundary := by
    rw [hAb i, hAb (other i)]
    apply disjoint_left.mpr
    rintro y (hyE | hyN) (hyE' | hyN')
    · exact disjoint_left.mp (hEdisother i) hyE hyE'
    · exact disjoint_left.mp (hcross i) hyE hyN'
    · have hh' := hcross (other i)
      rw [hoo i] at hh'
      exact disjoint_left.mp hh' hyE' hyN
    · exact disjoint_left.mp (hVdisother i) (hNV i hyN) (hNV (other i) hyN')
  have hRimA (i : Fin 2) : rim i ⊆ (A i).boundary := by
    intro y hy
    rw [hAb i]
    exact Or.inl (hRimE i hy)
  have hRimOutside (i : Fin 2) : rim i ⊆ (A (other i)).closedRegionᶜ := by
    intro y hy hyA
    have hyD : y ∈ Dtop (other i) := hcutTop (other i) ▸ ⟨hyA, hRimH i y hy⟩
    exact disjoint_left.mp (hDdisother i) (hRimD i hy) hyD
  let q0 : UnitCircle := circleDirection (0 : E2)
  have hRimNonempty (i : Fin 2) : (rim i).Nonempty :=
    ⟨T i ((q0 : E2), z), ((q0 : E2), z), ⟨q0.property, rfl⟩, rfl⟩
  have hdim : 1 < Module.rank ℝ E3 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E3]
  have hBout (i : Fin 2) : (A i).boundary ⊆ (A (other i)).closedRegionᶜ := by
    rcases (A (other i)).preconnected_subset_inside_or_outside
      ((A i).boundary_connected hdim).isPreconnected (hBdis i) with hin | hout
    · obtain ⟨y, hy⟩ := hRimNonempty i
      apply False.elim
      apply hRimOutside i hy
      rw [← (A (other i)).inside_union_boundary]
      exact Or.inl (hin (hRimA i hy))
    · exact hout
  have hIavoid (i : Fin 2) : Disjoint (A i).inside (A (other i)).boundary := by
    apply disjoint_left.mpr
    intro y hyi hyb
    have ho' := hBout (other i) hyb
    rw [hoo i] at ho'
    apply ho'
    rw [← (A i).inside_union_boundary]
    exact Or.inl hyi
  have hIdis (i : Fin 2) : Disjoint (A i).inside (A (other i)).inside := by
    apply disjoint_left.mpr
    intro y hyi hyj
    rcases (A (other i)).preconnected_subset_inside_or_outside
      (A i).inside_connected.isPreconnected (hIavoid i) with hin | hout
    · have hcl := closure_mono hin
      rw [(A i).closure_inside, (A (other i)).closure_inside] at hcl
      obtain ⟨p, hp⟩ := hRimNonempty i
      apply hRimOutside i hp
      apply hcl
      rw [← (A i).inside_union_boundary]
      exact Or.inr (hRimA i hp)
    · apply hout hyi
      rw [← (A (other i)).inside_union_boundary]
      exact Or.inl hyj
  have hAdisother (i : Fin 2) : Disjoint (A i).closedRegion (A (other i)).closedRegion := by
    apply disjoint_left.mpr
    intro y hyi hyj
    rw [← (A i).inside_union_boundary] at hyi
    rw [← (A (other i)).inside_union_boundary] at hyj
    rcases hyi with hyi | hyi <;> rcases hyj with hyj | hyj
    · exact disjoint_left.mp (hIdis i) hyi hyj
    · exact disjoint_left.mp (hIavoid i) hyi hyj
    · exact disjoint_left.mp (hIavoid (other i)) hyj (by simpa only [hoo] using hyi)
    · exact disjoint_left.mp (hBdis i) hyi hyj
  have hEclosed (i : Fin 2) : E i ⊆ (A i).closedRegion := by
    intro y hy
    rw [← (A i).inside_union_boundary, hAb i]
    exact Or.inr (Or.inl hy)
  have hinsideS (i : Fin 2) : Disjoint (A i).inside S := by
    apply disjoint_left.mpr
    intro y hyi hyS
    have hyA : y ∈ (A i).closedRegion := by
      rw [← (A i).inside_union_boundary]
      exact Or.inl hyi
    by_cases hyz : H y ≤ z
    · obtain ⟨q, rfl⟩ := hyS
      have hq : q ∈ ⋃ k : Fin 2, Es k := hsub ▸ hyz
      obtain ⟨k, hqk⟩ := mem_iUnion.mp hq
      have hyE : j q ∈ E k := ⟨q, hqk, rfl⟩
      by_cases hki : k = i
      · subst k
        exact disjoint_left.mp (A i).inside_disjoint_boundary hyi
          ((hAb i).symm ▸ Or.inl hyE)
      · have hko : k = other i := by
          fin_cases k <;> fin_cases i <;> first | rfl | exact False.elim (hki rfl)
        exact disjoint_left.mp (hAdisother i) hyA (hko ▸ hEclosed k hyE)
    · have hyz' : z < H y := lt_of_not_ge hyz
      have hyZ : H y ∈ Z := by
        have hu := hAupper i y hyA
        constructor <;> linarith [hlamd i]
      have hycircles : y ∈ ⋃ k : Fin 2, T k '' (sphere 0 1 ×ˢ ({H y} : Set ℝ)) :=
        hSband (H y) hyZ ▸ ⟨hyS, rfl⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hycircles
      obtain ⟨p, hp, hpy⟩ := hAi i hyi
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
      · have hko : k = other i := by
          fin_cases k <;> fin_cases i <;> first | rfl | exact False.elim (hki rfl)
        have hyVi : y ∈ V i := hTband i ⟨p,
          ⟨ball_subset_closedBall hp.1, hph.symm ▸ hyZ⟩, hpy⟩
        have hyVk : y ∈ V k := by
          obtain ⟨r, hr, hry⟩ := hk
          exact hTband k ⟨r, ⟨sphere_subset_closedBall hr.1, hr.2.symm ▸ hyZ⟩, hry⟩
        exact disjoint_left.mp (hVdisother i) hyVi (hko ▸ hyVk)
  have hret (i : Fin 2) : (A i).closedRegion ∩ (R ∪ E (other i)) ⊆ north i := by
    rintro y ⟨hyA, hyRet⟩
    have hyS : y ∈ S := hyRet.elim (fun h => h.1) (fun h => hES (other i) h)
    have hyB : y ∈ (A i).boundary := by
      rw [← (A i).inside_union_boundary] at hyA
      exact hyA.resolve_left (fun h => disjoint_left.mp (hinsideS i) h hyS)
    rw [hAb i] at hyB
    rcases hyB with hyE | hyN
    · rcases hyRet with hyR | hyOther
      · have hyz : H y = z := le_antisymm (hEh i y hyE) hyR.2
        exact hRimN i (hElevel i ▸ ⟨hyE, hyz⟩)
      · exact False.elim (disjoint_left.mp (hEdisother i) hyE hyOther)
    · exact hyN
  refine ⟨Q, A, o, ?_, hAdisother 0⟩
  intro i
  have hlt : lambda i * P.heightBound < tau := by linarith [hlamd i]
  have hlg : lambda i * P.heightBound < z - ell i := by linarith [hlamd i, hdel i]
  exact ⟨ho i, ho1 i, hlt, hlg, hchart i, hsource i, htarget i, hpoint i, hinv i,
    hAb i, hAi i, hAc i, hAupper i, hcuts i, (hcutTop i).trans (hdisc i),
    hpatch i, hinsideS i, hret i, hEN i⟩

end PoincareConjecture.M25.Topology3D
