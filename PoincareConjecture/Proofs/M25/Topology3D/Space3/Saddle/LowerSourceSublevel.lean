import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.NativeCapCore
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem SaddleLowerLevelData.source_sublevel_decomposition
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let E : Fin 2 → Set UnitTwoSphere := fun i =>
      (D.cap (W.label i)).sourceCap ∪
        W.leg i '' (univ ×ˢ Icc
          ((D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal) W.level)
    (∀ k : Fin D.capCount, (D.cap k).sign = 1 ↔ ∃ i : Fin 2, W.label i = k) ∧
    {q : UnitTwoSphere | ⟪(u : E3), j q⟫_ℝ ≤ W.level} = ⋃ i, E i ∧
    (∀ i : Fin 2, IsCompact (E i) ∧ IsConnected (E i)) ∧
    Disjoint (E 0) (E 1) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), j q⟫_ℝ
  let c := f D.point
  let seam : Fin D.capCount → ℝ := fun k =>
    (D.cap k).cutHeight + (D.cap k).sign * (D.cap k).removal
  let ell : Fin 2 → ℝ := fun i =>
    (D.cap (W.label i)).cutHeight + (D.cap (W.label i)).removal
  let I : Fin 2 → Set (UnitCircle × ℝ) := fun i => univ ×ˢ Icc (ell i) W.level
  let Leg : Fin 2 → Set UnitTwoSphere := fun i => W.leg i '' I i
  let E : Fin 2 → Set UnitTwoSphere := fun i => (D.cap (W.label i)).sourceCap ∪ Leg i
  change (∀ k : Fin D.capCount,
      (D.cap k).sign = 1 ↔ ∃ i : Fin 2, W.label i = k) ∧
    {q : UnitTwoSphere | f q ≤ W.level} = ⋃ i, E i ∧
    (∀ i : Fin 2, IsCompact (E i) ∧ IsConnected (E i)) ∧ Disjoint (E 0) (E 1)
  have hf : Continuous f := continuous_const.inner
    (collar_central_contMDiff psi hpsi).continuous
  have hseamell (i : Fin 2) : seam (W.label i) = ell i := by
    dsimp [seam, ell]
    rw [W.label_lower i, one_mul]
  have hell (i : Fin 2) : ell i < W.level := by
    rw [← hseamell i]
    exact W.lower_seams_lt_level (W.label i) (W.label_lower i)
  have hsource (i : Fin 2) : I i ⊆ (W.leg i).source := by
    have h := W.leg_source i
    change univ ×ˢ Icc (seam (W.label i)) W.level ⊆ (W.leg i).source at h
    simpa only [hseamell] using h
  have hcover : (⋃ i : Fin 2, Leg i) = D.sourceCore ∩ {q | f q ≤ W.level} := by
    have h := W.leg_cover
    change (⋃ i : Fin 2, W.leg i ''
      (univ ×ˢ Icc (seam (W.label i)) W.level)) = _ at h
    simpa only [hseamell] using h
  have hbottom (i : Fin 2) :
      range (fun theta : UnitCircle => W.leg i (theta, ell i)) =
        (D.cap (W.label i)).sourceSeam := by
    have h := W.leg_bottom i
    change range (fun theta : UnitCircle => W.leg i (theta, seam (W.label i))) = _ at h
    simpa only [hseamell] using h
  have hdis : Disjoint (Leg 0) (Leg 1) := by
    have h := W.leg_disjoint
    change Disjoint
      (W.leg 0 '' (univ ×ˢ Icc (seam (W.label 0)) W.level))
      (W.leg 1 '' (univ ×ˢ Icc (seam (W.label 1)) W.level)) at h
    simpa only [hseamell] using h
  have hlegcore (i : Fin 2) : Leg i ⊆ D.sourceCore := by
    intro q hq
    have hh : q ∈ ⋃ k : Fin 2, Leg k := mem_iUnion.mpr ⟨i, hq⟩
    rw [hcover] at hh
    exact hh.1
  have hlegheight (i : Fin 2) (p : UnitCircle × ℝ) (hp : p ∈ I i) :
      f (W.leg i p) = p.2 := W.leg_height i p (hsource i hp)
  have hseamcap (k : Fin D.capCount) : (D.cap k).sourceSeam ⊆ (D.cap k).sourceCap := by
    rintro q ⟨p, hp, rfl⟩
    exact ⟨p, hp.le, rfl⟩
  have hseamcore (k : Fin D.capCount) : (D.cap k).sourceSeam ⊆ D.sourceCore := by
    intro q hq
    have hh : q ∈ D.sourceCore ∩ (D.cap k).sourceCap := by
      rw [D.source_incidence k]
      exact hq
    exact hh.1
  have hseamleg (i : Fin 2) : (D.cap (W.label i)).sourceSeam ⊆ Leg i := by
    intro q hq
    rw [← hbottom i] at hq
    obtain ⟨theta, rfl⟩ := hq
    exact ⟨(theta, ell i), ⟨mem_univ _, le_rfl, (hell i).le⟩, rfl⟩
  have hcapinterior (k : Fin D.capCount) :
      Disjoint D.sourceCore (D.cap k).sourceCapInterior := by
    apply Set.disjoint_left.mpr
    intro q hqK hqI
    have hqC := (D.cap k).sourceCapInterior_subset hqI
    have hqS : q ∈ (D.cap k).sourceSeam := by
      rw [← D.source_incidence k]
      exact ⟨hqK, hqC⟩
    have hqD : q ∈ (D.cap k).sourceCap \ (D.cap k).sourceCapInterior := by
      rw [(D.cap k).sourceCap_diff_interior]
      exact hqS
    exact hqD.2 hqI
  have hplaced (k : Fin D.capCount) (p : UnitTwoSphere)
      (hp : (heightCoordinates (p : E3)).2 < (D.cap k).overlapWidth) :
      f ((D.cap k).sourceChart p) =
        (D.cap k).cutHeight + (D.cap k).sign *
          ((D.cap k).removal + (D.cap k).scale * ((D.cap k).profile.model p).2) := by
    let C := D.cap k
    have hT : ((C.profile.model p).1,
        C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model p).2)) ∈
        C.tube.source := C.tube_source
      ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le p), mem_univ _⟩
    change ⟪(u : E3), psi (C.sourceChart p, 0)⟫_ℝ = _
    rw [C.central_eq p hp, SurgeryCapProfile.capMap_apply, C.tube_height _ hT]
  have hseamheight (k : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap k).sourceSeam) : f q = seam k := by
    obtain ⟨p, hp, rfl⟩ := hq
    change (heightCoordinates (p : E3)).2 = 0 at hp
    let C := D.cap k
    have hm : (C.profile.model p).2 = 0 := by
      have hh := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far p (by rw [hp]; norm_num)
      simpa only [SurgeryCapProfile.model, hp] using congrArg Prod.snd hh
    rw [hplaced k p (by rw [hp]; exact C.overlap_pos)]
    change C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model p).2) =
      C.cutHeight + C.sign * C.removal
    rw [hm, mul_zero, add_zero]
  have hcapheight (k : Fin D.capCount) (q : UnitTwoSphere)
      (hq : q ∈ (D.cap k).sourceCap) :
      (D.cap k).sign * (f q - seam k) ≤ 0 := by
    obtain ⟨p, hp, rfl⟩ := hq
    change (heightCoordinates (p : E3)).2 ≤ 0 at hp
    let C := D.cap k
    have hm : (C.profile.model p).2 ≤ 0 := by
      exact (surgeryCapModel_snd_nonpos_iff C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.vertical_pos p).mpr hp
    have hsign : C.sign * C.sign = 1 := by nlinarith [sq_abs C.sign, C.sign_abs]
    have heq : C.sign * (f (C.sourceChart p) - seam k) =
        C.scale * (C.profile.model p).2 := by
      rw [hplaced k p (hp.trans_lt C.overlap_pos)]
      change C.sign *
        (C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model p).2) -
          (C.cutHeight + C.sign * C.removal)) = _
      calc
        _ = (C.sign * C.sign) * (C.scale * (C.profile.model p).2) := by ring
        _ = _ := by rw [hsign, one_mul]
    change C.sign * (f (C.sourceChart p) - seam k) ≤ 0
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hm
  have hupper (k : Fin D.capCount) (hk : (D.cap k).sign = -1) : c < seam k := by
    have hcut : c < (D.cap k).cutHeight := by
      rcases D.cut_side k with ⟨hs, _⟩ | ⟨_, hh⟩
      · rw [hk] at hs
        norm_num at hs
      · exact hh
    have hgap := D.cutRadius_lt_gap k
    change D.cutRadius k < |(D.cap k).cutHeight - c| at hgap
    rw [abs_of_pos (sub_pos.mpr hcut)] at hgap
    change c < (D.cap k).cutHeight + (D.cap k).sign * (D.cap k).removal
    rw [hk]
    nlinarith [D.removal_lt_cutRadius k]
  have hexhaust (k : Fin D.capCount) (hk : (D.cap k).sign = 1) :
      ∃ i : Fin 2, W.label i = k := by
    let C := D.cap k
    let theta : UnitCircle := circleDirection (0 : E2)
    let p0 : UnitTwoSphere := northSpherePoint theta.1
    let q0 := C.sourceChart p0
    have hp0 : (heightCoordinates (p0 : E3)).2 = 0 :=
      congrArg Prod.snd (northSpherePoint_equator theta)
    have hqS : q0 ∈ C.sourceSeam := ⟨p0, hp0, rfl⟩
    have hqK := hseamcore k hqS
    have hqf : f q0 = seam k := hseamheight k q0 hqS
    have hqtop : f q0 < W.level := by
      rw [hqf]
      exact W.lower_seams_lt_level k hk
    have hqLeg : q0 ∈ ⋃ i : Fin 2, Leg i := by
      rw [hcover]
      exact ⟨hqK, hqtop.le⟩
    obtain ⟨i, p, hp, hpq⟩ := mem_iUnion.mp hqLeg
    by_cases hik : W.label i = k
    · exact ⟨i, hik⟩
    have hpf : p.2 = f q0 := by
      have hh := hlegheight i p hp
      rw [hpq] at hh
      exact hh.symm
    have hpbot : ell i < p.2 := by
      apply lt_of_le_of_ne hp.2.1
      intro heq
      have hqSi : q0 ∈ (D.cap (W.label i)).sourceSeam := by
        rw [← hbottom i]
        refine ⟨p.1, ?_⟩
        have hpeq : (p.1, ell i) = p := Prod.ext rfl heq
        change W.leg i (p.1, ell i) = q0
        rw [hpeq]
        exact hpq
      exact Set.disjoint_left.mp (D.sourceCap_disjoint (W.label i) k hik)
        (hseamcap (W.label i) hqSi) (hseamcap k hqS)
    have hqtarget : q0 ∈ (W.leg i).target :=
      hpq ▸ (W.leg i).map_source (hsource i hp)
    let U : Set UnitTwoSphere :=
      (W.leg i).target ∩ {q | f q ∈ Ioo (ell i) W.level}
    have hU : IsOpen U :=
      (W.leg i).open_target.inter (isOpen_Ioo.preimage hf)
    have hqU : q0 ∈ U := ⟨hqtarget, hpf ▸ hpbot, hqtop⟩
    have hUK : U ⊆ D.sourceCore := by
      intro q hq
      have hinv : (W.leg i).symm q ∈ (W.leg i).source :=
        (W.leg i).map_target hq.1
      have hiheight : ((W.leg i).symm q).2 = f q := by
        have hh := W.leg_height i ((W.leg i).symm q) hinv
        rw [(W.leg i).right_inv hq.1] at hh
        exact hh.symm
      apply hlegcore i
      refine ⟨(W.leg i).symm q, ?_, (W.leg i).right_inv hq.1⟩
      exact ⟨mem_univ _, by rw [hiheight]; exact hq.2.1.le,
        by rw [hiheight]; exact hq.2.2.le⟩
    let gamma : ℝ → UnitTwoSphere := fun t => northSpherePoint ((1 + t) • theta.1)
    have hgamma : Continuous gamma :=
      northSpherePoint_contMDiff.continuous.comp
        ((continuous_const.add continuous_id).smul continuous_const)
    have hg0 : gamma 0 = p0 := by simp only [gamma, p0, add_zero, one_smul]
    have hp0src : p0 ∈ C.sourceChart.source :=
      C.south_mem_source p0 hp0.le
    have hc0 : ContinuousAt (fun t : ℝ => C.sourceChart (gamma t)) 0 := by
      apply (C.sourceChart.continuousOn.continuousAt
        (C.sourceChart.open_source.mem_nhds (hg0.symm ▸ hp0src))).comp hgamma.continuousAt
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, C.sourceChart (gamma t) ∈ U := by
      apply hc0.eventually_mem
      apply hU.mem_nhds
      simpa only [hg0] using hqU
    obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp hnear
    let t := eps / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have hgt : C.sourceChart (gamma t) ∈ U := hball (by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht]
      dsimp [t]
      linarith)
    have hnorm : ‖(1 + t) • theta.1‖ = 1 + t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + t),
        norm_eq_of_mem_sphere theta, mul_one]
    have hneg : (heightCoordinates (gamma t : E3)).2 < 0 := by
      by_contra hn
      have hh := (northSpherePoint_height_nonneg_iff ((1 + t) • theta.1)).mp
        (le_of_not_gt hn)
      rw [hnorm] at hh
      linarith
    have hgtI : C.sourceChart (gamma t) ∈ C.sourceCapInterior := ⟨gamma t, hneg, rfl⟩
    exact False.elim (Set.disjoint_left.mp (hcapinterior k) (hUK hgt) hgtI)
  have hlabels : ∀ k : Fin D.capCount,
      (D.cap k).sign = 1 ↔ ∃ i : Fin 2, W.label i = k := by
    intro k
    constructor
    · exact hexhaust k
    · rintro ⟨i, rfl⟩
      exact W.label_lower i
  have hlevel : {q : UnitTwoSphere | f q ≤ W.level} = ⋃ i, E i := by
    ext q
    constructor
    · intro hq
      have hqcover : q ∈ D.sourceCore ∪ ⋃ k, (D.cap k).sourceCap := by
        rw [D.source_cover]
        exact mem_univ q
      rcases hqcover with hqK | hqC
      · have hh : q ∈ ⋃ i : Fin 2, Leg i := by
          rw [hcover]
          exact ⟨hqK, hq⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp hh
        exact mem_iUnion.mpr ⟨i, Or.inr hi⟩
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hqC
        rcases D.cut_side k with ⟨hs, _⟩ | ⟨hs, _⟩
        · obtain ⟨i, hi⟩ := hexhaust k hs
          exact mem_iUnion.mpr ⟨i, Or.inl (hi.symm ▸ hk)⟩
        · have hh := hcapheight k q hk
          rw [hs] at hh
          have hc := hupper k hs
          have hz : W.level < c := W.level_lt_critical
          change f q ≤ W.level at hq
          nlinarith
    · intro hq
      obtain ⟨i, hi⟩ := mem_iUnion.mp hq
      rcases hi with hi | hi
      · have hh := hcapheight (W.label i) q hi
        rw [W.label_lower i, one_mul, hseamell i] at hh
        change f q ≤ W.level
        linarith [hell i]
      · obtain ⟨p, hp, rfl⟩ := hi
        change f (W.leg i p) ≤ W.level
        rw [hlegheight i p hp]
        exact hp.2.2
  have hcircle : IsConnected (univ : Set UnitCircle) := by
    have hdim : 1 < Module.rank ℝ E2 :=
      Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
    let : ConnectedSpace UnitCircle := Subtype.connectedSpace
      (isConnected_sphere hdim (0 : E2) (by norm_num : (0 : ℝ) ≤ 1))
    exact isConnected_univ
  have hLegCompact (i : Fin 2) : IsCompact (Leg i) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      ((W.leg i).continuousOn.mono (hsource i))
  have hLegConnected (i : Fin 2) : IsConnected (Leg i) :=
    (hcircle.prod (isConnected_Icc (hell i).le)).image (W.leg i)
      ((W.leg i).continuousOn.mono (hsource i))
  have hends (i : Fin 2) : IsCompact (E i) ∧ IsConnected (E i) := by
    obtain ⟨q, hq⟩ := (D.cap (W.label i)).sourceSeam_isConnected.nonempty
    exact ⟨(D.cap (W.label i)).sourceCap_isCompact.union (hLegCompact i),
      IsConnected.union ⟨q, hseamcap (W.label i) hq, hseamleg i hq⟩
        (D.cap (W.label i)).sourceCap_isConnected (hLegConnected i)⟩
  have hlabelne : W.label 0 ≠ W.label 1 := fun h =>
    (by norm_num : (0 : Fin 2) ≠ 1) (W.label_injective h)
  have hc0l1 : Disjoint (D.cap (W.label 0)).sourceCap (Leg 1) := by
    apply Set.disjoint_left.mpr
    intro q hqC hqL
    have hqS : q ∈ (D.cap (W.label 0)).sourceSeam := by
      rw [← D.source_incidence (W.label 0)]
      exact ⟨hlegcore 1 hqL, hqC⟩
    exact Set.disjoint_left.mp hdis (hseamleg 0 hqS) hqL
  have hl0c1 : Disjoint (Leg 0) (D.cap (W.label 1)).sourceCap := by
    apply Set.disjoint_left.mpr
    intro q hqL hqC
    have hqS : q ∈ (D.cap (W.label 1)).sourceSeam := by
      rw [← D.source_incidence (W.label 1)]
      exact ⟨hlegcore 0 hqL, hqC⟩
    exact Set.disjoint_left.mp hdis hqL (hseamleg 1 hqS)
  refine ⟨hlabels, hlevel, hends, ?_⟩
  apply Set.disjoint_left.mpr
  intro q hq0 hq1
  rcases hq0 with hq0 | hq0 <;> rcases hq1 with hq1 | hq1
  · exact Set.disjoint_left.mp (D.sourceCap_disjoint (W.label 0) (W.label 1) hlabelne)
      hq0 hq1
  · exact Set.disjoint_left.mp hc0l1 hq0 hq1
  · exact Set.disjoint_left.mp hl0c1 hq0 hq1
  · exact Set.disjoint_left.mp hdis hq0 hq1

end PoincareConjecture.M25.Topology3D
