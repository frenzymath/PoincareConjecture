import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.InnerSide
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.EndTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.LowerTubeBall
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

theorem exists_saddle_nested_staggered_lower_ends
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (i o : Fin 2) (hio : i ≠ o)
    (hnested : (W.disc i).closedRegion ⊆ (W.disc o).inside)
    (P : SurgeryCapProfile) (a eta : ℝ) (ha : 0 < a)
    (haell : a < W.level -
      ((D.cap (W.label o)).cutHeight + (D.cap (W.label o)).removal))
    (heta : 0 < eta) (heta_a : eta < a / 8)
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
    let t := W.level - a
    let L := T o '' (sphere (0 : E2) 1 ×ˢ Icc t W.level)
    let Elow := (fun q : UnitTwoSphere => T o
      (((D.cap (W.label o)).profile.model q).1,
        ell o + (D.cap (W.label o)).scale *
          ((D.cap (W.label o)).profile.model q).2)) ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∪
              T o '' (sphere (0 : E2) 1 ×ˢ Icc (ell o) t)
    let cut : Fin 2 → ℝ := fun k => if k = i then W.level else t
    let budget : Fin 2 → ℝ := fun k => if k = i then eta else a / 8
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    ∃ d : ℝ, 0 < d ∧ d < eta ∧ d < W.level - ell i ∧
      ∀ lambda : Fin 2 → ℝ, (∀ k, 0 < lambda k) →
        lambda i * P.heightBound < d →
        lambda o * P.heightBound < a / 8 →
        lambda o * P.heightBound < t - ell o →
      let north : Fin 2 → Set E3 := fun k =>
        (fun q : UnitTwoSphere =>
          T k ((P.model q).1, cut k + lambda k * (P.model q).2)) ''
            {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
      let south : Fin 2 → Set E3 := fun k =>
        (fun q : UnitTwoSphere =>
          T k ((P.model q).1, cut k + lambda k * (P.model q).2)) ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
      ∃ (N : Fin 2 → BallNeighborhoodChart E3 E3)
        (G : Fin 2 → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
        (C : Fin 2 → Set E3),
        (∀ k,
          (N k).boundary = south k ∪ north k ∧
          (N k).chart.source = {y : E3 | ((M (heightCoordinates y)).1,
            cut k + lambda k * (M (heightCoordinates y)).2) ∈ (T k).source} ∧
          (N k).chart.target = (T k).target ∧
          (∀ y : E3, (N k).chart y = T k ((M (heightCoordinates y)).1,
            cut k + lambda k * (M (heightCoordinates y)).2)) ∧
          (∀ y : E3, (N k).chart.symm y = heightCoordinates.symm
            (M.symm (((T k).symm y).1, (((T k).symm y).2 - cut k) / lambda k))) ∧
          (N k).closedRegion ⊆ {y : E3 | |H y - cut k| < budget k} ∧
          north k = (N k).chart ''
            {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} ∧
          south k ∩ north k = T k '' (sphere (0 : E2) 1 ×ˢ ({cut k} : Set ℝ)) ∧
          IsCompact (C k) ∧
          tsupport (fun y => G k y - y) ⊆ C k ∧
          tsupport (fun y => (G k).symm y - y) ⊆ C k) ∧
        E o = Elow ∪ L ∧ IsCompact R ∧ IsCompact L ∧
        Disjoint (N i).closedRegion (N o).closedRegion ∧
        G i '' E i = south i ∧ (G i).symm '' south i = E i ∧
        G o '' Elow = south o ∧ (G o).symm '' south o = Elow ∧
        (∀ y ∈ north i ∪ (R ∪ E o) ∪ {y : E3 | W.level + 2 * eta ≤ H y},
          G i y = y ∧ (G i).symm y = y) ∧
        C i ⊆ (north i ∪ (R ∪ E o) ∪ {y : E3 | W.level + 2 * eta ≤ H y})ᶜ ∧
        C i ⊆ {y : E3 | H y < W.level + 2 * eta} ∧
        (∀ y ∈ north o ∪ (R ∪ L ∪ (N i).closedRegion) ∪
            {y : E3 | t + a / 2 ≤ H y},
          G o y = y ∧ (G o).symm y = y) ∧
        C o ⊆ (north o ∪ (R ∪ L ∪ (N i).closedRegion) ∪
          {y : E3 | t + a / 2 ≤ H y})ᶜ ∧
        C o ⊆ {y : E3 | H y < t + a / 2} ∧
        let Gtotal := (G i).trans (G o)
        Gtotal '' S = (R ∪ L) ∪ south i ∪ south o ∧
        Gtotal.symm '' ((R ∪ L) ∪ south i ∪ south o) = S ∧
        (∀ y ∈ R ∪ L, Gtotal y = y ∧ Gtotal.symm y = y) ∧
        IsCompact (C i ∪ C o) ∧ (C i ∪ C o) ⊆ (R ∪ L)ᶜ ∧
        (C i ∪ C o) ⊆ {y : E3 | H y < W.level + 2 * eta} ∧
        tsupport (fun y => Gtotal y - y) ⊆ C i ∪ C o ∧
        tsupport (fun y => Gtotal.symm y - y) ⊆ C i ∪ C o := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  change ∀ k p, p ∈ (T k).source → H (T k p) = p.2 at hh
  let z := W.level
  let S : Set E3 := range j
  let R : Set E3 := S ∩ {y : E3 | z ≤ H y}
  let ell : Fin 2 → ℝ := fun k =>
    (D.cap (W.label k)).cutHeight + (D.cap (W.label k)).removal
  let Es : Fin 2 → Set UnitTwoSphere := fun k =>
    (D.cap (W.label k)).sourceCap ∪ W.leg k '' (univ ×ˢ Icc (ell k) z)
  let E : Fin 2 → Set E3 := fun k => j '' Es k
  let t := z - a
  let L := T o '' (sphere (0 : E2) 1 ×ˢ Icc t z)
  let lower : Fin 2 → Set E3 := fun k =>
    (fun q : UnitTwoSphere => T k (((D.cap (W.label k)).profile.model q).1,
      ell k + (D.cap (W.label k)).scale * ((D.cap (W.label k)).profile.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let Elow := lower o ∪ T o '' (sphere (0 : E2) 1 ×ˢ Icc (ell o) t)
  let cut : Fin 2 → ℝ := fun k => if k = i then z else t
  let budget : Fin 2 → ℝ := fun k => if k = i then eta else a / 8
  have hoi : o ≠ i := hio.symm
  have hlabels (k : Fin 2) : k = i ∨ k = o := by omega
  have htz : t < z := sub_lt_self z ha
  have hellt : ell o < t := by
    change a < z - ell o at haell
    dsimp [t]
    linarith
  have hell (k : Fin 2) : ell k < z := by
    simpa only [ell, W.label_lower k, one_mul] using
      W.lower_seams_lt_level (W.label k) (W.label_lower k)
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  obtain ⟨_, hsub, hEs, _⟩ :=
    SaddleLowerLevelData.source_sublevel_decomposition psi hpsi u D W
  change {q : UnitTwoSphere | H (j q) ≤ z} = ⋃ k : Fin 2, Es k at hsub
  have hES (k : Fin 2) : E k ⊆ S := by
    rintro y ⟨q, _, rfl⟩
    exact mem_range_self q
  have hS : S = R ∪ E i ∪ E o := by
    ext y
    constructor
    · intro hy
      by_cases hzy : z ≤ H y
      · exact Or.inl (Or.inl ⟨hy, hzy⟩)
      · obtain ⟨q, rfl⟩ := hy
        have hq : q ∈ ⋃ k : Fin 2, Es k := hsub ▸ (lt_of_not_ge hzy).le
        obtain ⟨k, hk⟩ := mem_iUnion.mp hq
        rcases hlabels k with rfl | rfl
        · exact Or.inl (Or.inr ⟨q, hk, rfl⟩)
        · exact Or.inr ⟨q, hk, rfl⟩
    · rintro ((hy | hy) | hy)
      · exact hy.1
      · exact hES i hy
      · exact hES o hy
  have hR : IsCompact R :=
    (isCompact_range hj).inter_right (isClosed_le continuous_const H.continuous)
  have hEcompact (k : Fin 2) : IsCompact (E k) := (hEs k).1.image hj
  have hL : IsCompact L :=
    ((isCompact_sphere (0 : E2) 1).prod isCompact_Icc).image_of_continuousOn
      ((hT o).continuousOn.mono (fun _ hp => hs o
        ⟨sphere_subset_closedBall hp.1, mem_univ _⟩))
  have hEformula (k : Fin 2) :
      E k = lower k ∪ T k '' (sphere (0 : E2) 1 ×ˢ Icc (ell k) z) := by
    have hcap : lower k = j '' (D.cap (W.label k)).sourceCap := by
      rw [SurgeryCapTag.sourceCap, image_image]
      exact image_congr (fun q hq => hold k q hq)
    have hleg : T k '' (sphere (0 : E2) 1 ×ˢ Icc (ell k) z) =
        j '' (W.leg k '' (univ ×ˢ Icc (ell k) z)) := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hp' : T k p ∈ T k '' (sphere 0 1 ×ˢ ({p.2} : Set ℝ)) :=
          ⟨p, ⟨hp.1, rfl⟩, rfl⟩
        rw [hcircle k p.2 ⟨hp.2.1, hp.2.2.trans (by linarith [hgamma k])⟩] at hp'
        obtain ⟨q, hq⟩ := hp'
        exact ⟨W.leg k (q, p.2), ⟨(q, p.2), ⟨mem_univ _, hp.2⟩, rfl⟩, hq⟩
      · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
        have hp' : j (W.leg k p) ∈ T k '' (sphere 0 1 ×ˢ ({p.2} : Set ℝ)) := by
          rw [hcircle k p.2 ⟨hp.2.1, hp.2.2.trans (by linarith [hgamma k])⟩]
          exact ⟨p.1, rfl⟩
        obtain ⟨r, hr, hEq⟩ := hp'
        exact ⟨r, ⟨hr.1, hr.2.symm ▸ hp.2⟩, hEq⟩
    change j '' ((D.cap (W.label k)).sourceCap ∪ _) = _
    rw [image_union, hcap, hleg]
  have hsplit : E o = Elow ∪ L := by
    rw [hEformula o]
    change lower o ∪ T o '' (sphere 0 1 ×ˢ Icc (ell o) z) =
      (lower o ∪ T o '' (sphere 0 1 ×ˢ Icc (ell o) t)) ∪ L
    have hI : Icc (ell o) z = Icc (ell o) t ∪ Icc t z := by
      ext s
      simp only [mem_Icc, mem_union]
      constructor
      · intro hs
        rcases le_total s t with hst | hts
        · exact Or.inl ⟨hs.1, hst⟩
        · exact Or.inr ⟨hts, hs.2⟩
      · rintro (hs | hs)
        · exact ⟨hs.1, hs.2.trans htz.le⟩
        · exact ⟨hellt.le.trans hs.1, hs.2⟩
    rw [hI, prod_union, image_union, ← union_assoc]
  have hLE : L ⊆ E o := by
    rw [hsplit]
    exact subset_union_right
  obtain ⟨d, hd, hdeta, hdell, hinner⟩ :=
    exists_saddle_nested_inner_end_scale_bound psi hpsi u D W i o hio hnested P eta heta
      T gamma hgamma hs hT hTi hh hold hcircle hdisc
  refine ⟨d, hd, hdeta, hdell, ?_⟩
  intro lambda hlambda hli hlo hlogap
  let ni := (fun q : UnitTwoSphere => T i
    ((P.model q).1, z + lambda i * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let si := (fun q : UnitTwoSphere => T i
    ((P.model q).1, z + lambda i * (P.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let no := (fun q : UnitTwoSphere => T o
    ((P.model q).1, t + lambda o * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let so := (fun q : UnitTwoSphere => T o
    ((P.model q).1, t + lambda o * (P.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  obtain ⟨_, Ai, oi, hoi0, hoi1, _, _, _, _, _, hAib, _, hAic,
    hAicut, hAipatch, _, _, hAiavoid, hAirim⟩ := hinner (lambda i) (hlambda i) hli
  have hAifill (s : ℝ) (hs' : s ∈ Icc (ell i) z) :
      T i '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆ Ai.closedRegion :=
    fun _ hy => ((hAicut s hs').2.superset hy).1
  have hAiupper : Ai.closedRegion ⊆ {y : E3 | H y < z + 2 * eta} := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := hAic hy
    change H (T i p) < z + 2 * eta
    rw [hh i p (hs i ⟨hp.1, mem_univ _⟩)]
    have hbound : p.2 ≤ z + lambda i * P.heightBound := hp.2.2
    linarith
  obtain ⟨Ni, Gi, Ci, hNib, hNis, hNit, hNip, hNiinv, _, hNishort,
    hNin, hNirim, hGiE, hGii, hGif, hCi, hCis, hCib, hGis, hGiis⟩ :=
    exists_saddle_profile_end_replacement_below P u (T i) (hs i) (hT i) (hTi i) (hh i)
      Ai (ell i) z (lambda i) eta (z + 2 * eta) oi (hlambda i)
      (hli.trans hdell) (hli.trans hdeta) hoi0 (by linarith)
      (E i) (R ∪ E o) (hR.union (hEcompact o)).isClosed hAifill hAib hAipatch
      hAirim hAiavoid hAiupper
  change Ni.boundary = si ∪ ni at hNib
  change Gi '' E i = si at hGiE
  change Gi.symm '' si = E i at hGii
  have hNiLower (y : E3) (hy : y ∈ Ni.closedRegion) : z - eta < H y := by
    have hshort : |H y - z| < eta := hNishort hy
    have h := (abs_lt.mp hshort).1
    linarith
  have hsiNi : si ⊆ Ni.closedRegion := by
    intro y hy
    rw [← Ni.inside_union_boundary, hNib]
    exact Or.inr (Or.inl hy)
  obtain ⟨_, Ao, oo, hoo, hoo1, _, _, _, _, _, hAob, _, hAoc,
    hAocut, hAopatch, hAorim, _, hAoL⟩ :=
    exists_saddle_lower_tube_end_ball_with_retained_cylinder
      (D.cap (W.label o)).profile P u (T o) (hs o) (hT o) (hTi o) (hh o)
      (ell o) t (D.cap (W.label o)).scale (lambda o) z hellt
      (D.cap (W.label o)).scale_pos (hlambda o)
  change Ao.boundary = Elow ∪ no at hAob
  have hAofill (s : ℝ) (hs' : s ∈ Icc (ell o) t) :
      T o '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆ Ao.closedRegion :=
    fun _ hy => ((hAocut s hs').2.superset hy).1
  have hAoUpper (y : E3) (hy : y ∈ Ao.closedRegion) : H y < t + a / 8 := by
    obtain ⟨p, hp, rfl⟩ := hAoc hy
    rw [hh o p (hs o ⟨hp.1, mem_univ _⟩)]
    have hbound : p.2 ≤ t + lambda o * P.heightBound := hp.2.2
    linarith
  have hAoavoid : Ao.closedRegion ∩ (R ∪ L ∪ Ni.closedRegion) ⊆ no := by
    rintro y ⟨hyA, (hyR | hyL) | hyNi⟩
    · have hupper := hAoUpper y hyA
      have hlower : z ≤ H y := hyR.2
      dsimp [t] at hupper
      linarith
    · exact hAoL ⟨hyA, hyL⟩
    · have hupper := hAoUpper y hyA
      have hlower := hNiLower y hyNi
      dsimp [t] at hupper
      linarith
  have hAoHalfspace : Ao.closedRegion ⊆ {y : E3 | H y < t + a / 2} := by
    intro y hy
    have hupper := hAoUpper y hy
    change H y < t + a / 2
    linarith
  obtain ⟨No, Go, Co, hNob, hNos, hNot, hNop, hNoinv, _, hNoshort,
    hNon, hNorim, hGoE, hGoi, hGof, hCo, hCos, hCob, hGos, hGois⟩ :=
    exists_saddle_profile_end_replacement_below P u (T o) (hs o) (hT o) (hTi o) (hh o)
      Ao (ell o) t (lambda o) (a / 8) (t + a / 2) oo (hlambda o)
      hlogap hlo hoo (by linarith) Elow (R ∪ L ∪ Ni.closedRegion)
      ((hR.union hL).union Ni.closedRegion_compact).isClosed hAofill hAob hAopatch
      hAorim hAoavoid hAoHalfspace
  change No.boundary = so ∪ no at hNob
  change Go '' Elow = so at hGoE
  change Go.symm '' so = Elow at hGoi
  have hNdis : Disjoint Ni.closedRegion No.closedRegion := by
    apply disjoint_left.mpr
    intro y hyi hyo
    have hi' := hNiLower y hyi
    have hshort : |H y - t| < a / 8 := hNoshort hyo
    have ho' := (abs_lt.mp hshort).2
    dsimp [t] at ho'
    linarith
  have hGiRet (y : E3) (hy : y ∈ R ∪ L) : Gi y = y ∧ Gi.symm y = y := by
    apply hGif y
    apply Or.inl
    apply Or.inr
    exact hy.elim Or.inl (fun h => Or.inr (hLE h))
  have hGoRet (y : E3) (hy : y ∈ R ∪ L) : Go y = y ∧ Go.symm y = y :=
    hGof y (Or.inl (Or.inr (Or.inl hy)))
  have hGoSi (y : E3) (hy : y ∈ si) : Go y = y ∧ Go.symm y = y :=
    hGof y (Or.inl (Or.inr (Or.inr (hsiNi hy))))
  have hfixedImage
      (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (X : Set E3)
      (hfix : ∀ y ∈ X, F y = y) : F '' X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hfix x hx] using hx
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  have hGiR : Gi '' R = R :=
    hfixedImage Gi R (fun y hy => (hGiRet y (Or.inl hy)).1)
  have hGiEo : Gi '' E o = E o :=
    hfixedImage Gi (E o) (fun y hy => (hGif y (Or.inl (Or.inr (Or.inr hy)))).1)
  have hGoR : Go '' R = R :=
    hfixedImage Go R (fun y hy => (hGoRet y (Or.inl hy)).1)
  have hGoL : Go '' L = L :=
    hfixedImage Go L (fun y hy => (hGoRet y (Or.inr hy)).1)
  have hGosi : Go '' si = si :=
    hfixedImage Go si (fun y hy => (hGoSi y hy).1)
  have hGiS : Gi '' S = R ∪ si ∪ E o := by
    rw [hS, image_union, image_union, hGiR, hGiE, hGiEo]
  let Gtotal := Gi.trans Go
  have htotal : Gtotal '' S = (R ∪ L) ∪ si ∪ so := by
    calc
      Gtotal '' S = Go '' (Gi '' S) := by rw [image_image]; rfl
      _ = Go '' (R ∪ si ∪ E o) := by rw [hGiS]
      _ = Go '' (R ∪ si ∪ (Elow ∪ L)) := by rw [hsplit]
      _ = (R ∪ L) ∪ si ∪ so := by
        rw [image_union, image_union, image_union, hGoR, hGosi, hGoE, hGoL]
        ext y
        simp only [mem_union]
        tauto
  have htotalInv : Gtotal.symm '' ((R ∪ L) ∪ si ∪ so) = S := by
    rw [← htotal]
    exact Gtotal.symm_image_image S
  have htotalFix (y : E3) (hy : y ∈ R ∪ L) :
      Gtotal y = y ∧ Gtotal.symm y = y := by
    have hi' := hGiRet y hy
    have ho' := hGoRet y hy
    change Go (Gi y) = y ∧ Gi.symm (Go.symm y) = y
    rw [hi'.1, ho'.1, ho'.2, hi'.2]
    exact ⟨rfl, rfl⟩
  have hCC : IsCompact (Ci ∪ Co) := hCi.union hCo
  have hCCret : Ci ∪ Co ⊆ (R ∪ L)ᶜ := by
    rintro y (hy | hy) hyRet
    · apply hCis hy
      apply Or.inl
      apply Or.inr
      exact hyRet.elim Or.inl (fun h => Or.inr (hLE h))
    · exact hCos hy (Or.inl (Or.inr (Or.inl hyRet)))
  have hCCbelow : Ci ∪ Co ⊆ {y : E3 | H y < z + 2 * eta} := by
    rintro y (hy | hy)
    · exact hCib hy
    · have h : H y < t + a / 2 := hCob hy
      change H y < z + 2 * eta
      dsimp [t] at h
      linarith
  have hfar (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (K : Set E3) (hsupp : tsupport (fun y => F y - y) ⊆ K)
      (y : E3) (hy : y ∉ K) : F y = y := by
    apply sub_eq_zero.mp
    exact image_eq_zero_of_notMem_tsupport (f := fun y => F y - y)
      (fun h => hy (hsupp h))
  have htotalFar (y : E3) (hy : y ∉ Ci ∪ Co) :
      Gtotal y = y ∧ Gtotal.symm y = y := by
    have hi' := hfar Gi Ci hGis y (fun h => hy (Or.inl h))
    have hii' := hfar Gi.symm Ci hGiis y (fun h => hy (Or.inl h))
    have ho' := hfar Go Co hGos y (fun h => hy (Or.inr h))
    have hoi' := hfar Go.symm Co hGois y (fun h => hy (Or.inr h))
    change Go (Gi y) = y ∧ Gi.symm (Go.symm y) = y
    rw [hi', ho', hoi', hii']
    exact ⟨rfl, rfl⟩
  have htotalSupp : tsupport (fun y => Gtotal y - y) ⊆ Ci ∪ Co := by
    apply closure_minimal ?_ hCC.isClosed
    intro y hy
    by_contra hyC
    exact hy (sub_eq_zero.mpr (htotalFar y hyC).1)
  have htotalInvSupp : tsupport (fun y => Gtotal.symm y - y) ⊆ Ci ∪ Co := by
    apply closure_minimal ?_ hCC.isClosed
    intro y hy
    by_contra hyC
    exact hy (sub_eq_zero.mpr (htotalFar y hyC).2)
  let N : Fin 2 → BallNeighborhoodChart E3 E3 := fun k => if k = i then Ni else No
  let G : Fin 2 → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun k => if k = i then Gi else Go
  let C : Fin 2 → Set E3 := fun k => if k = i then Ci else Co
  refine ⟨N, G, C, ?_, ?_⟩
  · intro k
    rcases hlabels k with rfl | rfl
    · simp only [N, G, C, if_pos rfl]
      exact ⟨hNib, hNis, hNit, hNip, hNiinv, hNishort, hNin, hNirim, hCi, hGis, hGiis⟩
    · simp only [N, G, C, if_neg hoi]
      exact ⟨hNob, hNos, hNot, hNop, hNoinv, hNoshort, hNon, hNorim, hCo, hGos, hGois⟩
  · simp only [N, G, C, if_pos rfl, if_neg hoi]
    exact ⟨hsplit, hR, hL, hNdis, hGiE, hGii, hGoE, hGoi,
      hGif, hCis, hCib, hGof, hCos, hCob, htotal, htotalInv,
      htotalFix, hCC, hCCret, hCCbelow, htotalSupp, htotalInvSupp⟩

end PoincareConjecture.M25.Topology3D
