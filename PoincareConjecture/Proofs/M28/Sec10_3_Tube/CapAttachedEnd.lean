import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapOverlapCompactEnd
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereCoordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

private theorem half_tail_not_subset_compact (T : OpenCylinderModel U)
    (side : Bool) {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ x ∈ T.tail side (1 / 2), x ∉ K := by
  obtain ⟨a, b, ha, _, hb, hcapture⟩ := T.exists_compactSlab_capturing hK hKU
  cases side
  · obtain ⟨x, hx⟩ := T.tail_nonempty false
      (lt_min ha (by norm_num : (0 : ℝ) < 1 / 2))
      ((min_le_right a (1 / 2 : ℝ)).trans_lt (by norm_num))
    have hx' := (T.mem_tail_iff_m28 false (lt_min ha (by norm_num))
      ((min_le_right a (1 / 2 : ℝ)).trans_lt (by norm_num))).mp hx
    refine ⟨x, (T.mem_tail_iff_m28 false (by norm_num) (by norm_num)).mpr
      ⟨hx'.1, hx'.2.trans_le (min_le_right _ _)⟩, ?_⟩
    intro hxK
    have hslab := (T.mem_compactSlab_iff ha hb).mp (hcapture hxK)
    exact (not_lt_of_ge hslab.2.1) (hx'.2.trans_le (min_le_left _ _))
  · obtain ⟨x, hx⟩ := T.tail_nonempty true
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right b (1 / 2 : ℝ)))
      (max_lt hb (by norm_num : (1 / 2 : ℝ) < 1))
    have hx' := (T.mem_tail_iff_m28 true
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right b (1 / 2 : ℝ)))
      (max_lt hb (by norm_num))).mp hx
    refine ⟨x, (T.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hx'.1, (le_max_right _ _).trans_lt hx'.2⟩, ?_⟩
    intro hxK
    have hslab := (T.mem_compactSlab_iff ha hb).mp (hcapture hxK)
    exact (not_lt_of_ge hslab.2.2) ((le_max_left _ _).trans_lt hx'.2)

end PoincareConjecture.OpenCylinderModel

namespace PoincareConjecture.CapTubeAttachment

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  {X : Set M} {cap : CapCertificate g} {tube : EpsilonTubeCertificate g X}
  {side : Bool}

theorem exists_compact_attached_tail (A : CapTubeAttachment cap tube side)
    {S : Set M} (hS : SmoothSphereIsotopicIn tube.carrier S tube.cylinder.middleSphere)
    (hcapS : Disjoint cap.carrier S) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      IsCompact (closure (tube.cylinder.tail side a)) ∧
      closure (tube.cylinder.tail side a) ⊆ cap.carrier := by
  classical
  let U : TopologicalSpace.Opens M := ⟨tube.carrier, tube.carrier_open⟩
  let O : Set M := cap.carrier ∩ tube.carrier
  let E := A.overlap_model
  let T := tube.cylinder
  obtain ⟨φ, lo, hi, hlo, hlohalf, hhalfhi, hhi, hsphere, hfix⟩ :=
    T.exists_isotopic_sphere_coordinates (U := U) hS
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  let : ConnectedSpace (Ioo (0 : ℝ) 1) := Subtype.connectedSpace (isConnected_Ioo zero_lt_one)
  let : ConnectedSpace O := E.homeomorph.surjective.connectedSpace E.homeomorph.continuous
  let ι : O → U := fun x => ⟨x, x.property.2⟩
  let f : O → ℝ := fun x => ((φ (ι x)).2 : ℝ)
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hf : Continuous f := continuous_subtype_val.comp
    ((continuous_snd.comp φ.continuous).comp hι)
  have hfne : ∀ x ∈ (univ : Set O), f x ≠ 1 / 2 := by
    intro x _ heq
    exact disjoint_left.mp hcapS x.property.1 ((hsphere (ι x)).mp heq)
  obtain ⟨a₀, ha₀, hattached⟩ := A.tube_tail
  have hbound : ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∀ x ∈ O, if side then b ≤ (T.inverse x).2 else (T.inverse x).2 ≤ b := by
    cases side
    · obtain ⟨p, hp⟩ := T.tail_nonempty false (lt_min ha₀.1 hlo)
        ((min_le_left a₀ lo).trans_lt ha₀.2)
      have hp' := (T.mem_tail_iff_m28 false (lt_min ha₀.1 hlo)
        ((min_le_left a₀ lo).trans_lt ha₀.2)).mp hp
      have hpT : p ∈ T.tail false a₀ := (T.mem_tail_iff_m28 false ha₀.1 ha₀.2).mpr
        ⟨hp'.1, hp'.2.trans_le (min_le_left _ _)⟩
      let pO : O := ⟨p, hattached hpT, hp'.1⟩
      have hpheight : f pO < 1 / 2 := by
        change ((φ (ι pO)).2 : ℝ) < 1 / 2
        rw [hfix (ι pO) (Or.inl (hp'.2.trans_le (min_le_right _ _)))]
        exact (hp'.2.trans_le (min_le_right _ _)).trans hlohalf
      have hnegative (x : O) : f x < 1 / 2 :=
        isPreconnected_univ.gt_of_ne hf.continuousOn hfne
          ⟨pO, mem_univ _, hpheight⟩ (mem_univ x)
      refine ⟨hi, (by norm_num : (0 : ℝ) < 1 / 2).trans hhalfhi, hhi, ?_⟩
      intro x hx
      by_contra h
      have hxhi : hi < (T.inverse x).2 := lt_of_not_ge h
      have hfx := hnegative ⟨x, hx⟩
      change ((φ (ι ⟨x, hx⟩)).2 : ℝ) < 1 / 2 at hfx
      rw [hfix (ι ⟨x, hx⟩) (Or.inr hxhi)] at hfx
      exact (not_lt_of_ge (hhalfhi.trans hxhi).le) hfx
    · obtain ⟨p, hp⟩ := T.tail_nonempty true
        (ha₀.1.trans_le (le_max_left a₀ hi)) (max_lt ha₀.2 hhi)
      have hp' := (T.mem_tail_iff_m28 true
        (ha₀.1.trans_le (le_max_left a₀ hi)) (max_lt ha₀.2 hhi)).mp hp
      have hpT : p ∈ T.tail true a₀ := (T.mem_tail_iff_m28 true ha₀.1 ha₀.2).mpr
        ⟨hp'.1, (le_max_left _ _).trans_lt hp'.2⟩
      let pO : O := ⟨p, hattached hpT, hp'.1⟩
      have hpheight : 1 / 2 < f pO := by
        change 1 / 2 < ((φ (ι pO)).2 : ℝ)
        rw [hfix (ι pO) (Or.inr ((le_max_right _ _).trans_lt hp'.2))]
        exact hhalfhi.trans ((le_max_right _ _).trans_lt hp'.2)
      have hpositive (x : O) : 1 / 2 < f x :=
        isPreconnected_univ.lt_of_ne hf.continuousOn hfne
          ⟨pO, mem_univ _, hpheight⟩ (mem_univ x)
      refine ⟨lo, hlo, hlohalf.trans (by norm_num), ?_⟩
      intro x hx
      by_contra h
      have hxlo : (T.inverse x).2 < lo := lt_of_not_ge h
      have hfx := hpositive ⟨x, hx⟩
      change 1 / 2 < ((φ (ι ⟨x, hx⟩)).2 : ℝ) at hfx
      rw [hfix (ι ⟨x, hx⟩) (Or.inl hxlo)] at hfx
      exact (not_lt_of_ge (hxlo.trans hlohalf).le) hfx
  obtain ⟨b, hb, hb', hbound⟩ := hbound
  obtain ⟨q, _, _, hWcompact, hWcap, overlapSide, hcapture⟩ :=
    A.exists_compact_overlap_end
  let W := closure (cap.closed_core ∪ cap.end_neck.region (-cap.epsilon⁻¹) q)
  obtain ⟨mlo, mhi, hmlo, _, hmhi, hmiddle⟩ :=
    T.exists_compactSlab_capturing E.isCompact_middleSphere
      (E.middleSphere_subset.trans inter_subset_right)
  have hfinish {a : ℝ} (ha : 0 < a) (ha' : a < 1)
      (hAO : T.tail side a ⊆ O)
      (havoid : ∀ x ∈ T.tail side a, (E.inverse x).2 ≠ 1 / 2)
      (hmeet : (T.tail side a ∩ E.tail overlapSide (1 / 2)).Nonempty) :
      IsCompact (closure (T.tail side a)) ∧ closure (T.tail side a) ⊆ cap.carrier := by
    have hcontinuous : ContinuousOn (fun x => (E.inverse x).2) (T.tail side a) :=
      (continuous_snd.comp_continuousOn E.inverse_smooth.continuousOn).mono hAO
    obtain ⟨x₀, hx₀, hx₀E⟩ := hmeet
    have hx₀' := (E.mem_tail_iff_m28 overlapSide (by norm_num) (by norm_num)).mp hx₀E
    have hsub : T.tail side a ⊆ W := by
      intro x hx
      apply hcapture
      apply (E.mem_tail_iff_m28 overlapSide (by norm_num) (by norm_num)).mpr
      refine ⟨hAO hx, ?_⟩
      cases overlapSide
      · exact (T.isPreconnected_tail side ha ha').gt_of_ne hcontinuous havoid
          ⟨x₀, hx₀, hx₀'.2⟩ hx
      · exact (T.isPreconnected_tail side ha ha').lt_of_ne hcontinuous havoid
          ⟨x₀, hx₀, hx₀'.2⟩ hx
    have hcl : closure (T.tail side a) ⊆ W := closure_minimal hsub isClosed_closure
    exact ⟨hWcompact.of_isClosed_subset isClosed_closure hcl, hcl.trans hWcap⟩
  cases side
  · obtain ⟨a, ha, hamax⟩ := exists_between (lt_min ha₀.1 (lt_min hmlo hb))
    have haa₀ : a < a₀ := hamax.trans_le (min_le_left _ _)
    have hamlo : a < mlo := (hamax.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hab : a < b := (hamax.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have ha' : a < 1 := hab.trans hb'
    have hAO : T.tail false a ⊆ O := by
      intro x hx
      have hx' := (T.mem_tail_iff_m28 false ha ha').mp hx
      exact ⟨hattached ((T.mem_tail_iff_m28 false ha₀.1 ha₀.2).mpr
        ⟨hx'.1, hx'.2.trans haa₀⟩), hx'.1⟩
    have havoid : ∀ x ∈ T.tail false a, (E.inverse x).2 ≠ 1 / 2 := by
      intro x hx heq
      have hxmiddle := (E.mem_middleSphere_iff (hAO hx)).mpr heq
      have hslab := (T.mem_compactSlab_iff hmlo hmhi).mp (hmiddle hxmiddle)
      have hx' := (T.mem_tail_iff_m28 false ha ha').mp hx
      exact (not_lt_of_ge hslab.2.1) (hx'.2.trans hamlo)
    let K := W ∩ T.compactSlab a b
    have hK : IsCompact K := hWcompact.inter (T.isCompact_compactSlab ha hb')
    have hKO : K ⊆ O := by
      intro x hx
      exact ⟨hWcap hx.1, T.compactSlab_subset ha hb' hx.2⟩
    obtain ⟨x, hxE, hxK⟩ := E.half_tail_not_subset_compact overlapSide hK hKO
    have hxO := E.tail_subset_m28 overlapSide (by norm_num) (by norm_num) hxE
    have hxW := hcapture hxE
    have hxT : x ∈ T.tail false a := by
      apply (T.mem_tail_iff_m28 false ha ha').mpr
      refine ⟨hxO.2, ?_⟩
      by_contra h
      apply hxK
      exact ⟨hxW, (T.mem_compactSlab_iff ha hb').mpr
        ⟨hxO.2, le_of_not_gt h, hbound x hxO⟩⟩
    exact ⟨a, ha, ha', hfinish ha ha' hAO havoid ⟨x, hxT, hxE⟩⟩
  · obtain ⟨a, hmaxa, ha'⟩ := exists_between (max_lt ha₀.2 (max_lt hmhi hb'))
    have ha₀a : a₀ < a := (le_max_left _ _).trans_lt hmaxa
    have hmhi_a : mhi < a := (le_max_left _ _).trans_lt
      ((le_max_right _ _).trans_lt hmaxa)
    have hba : b < a := (le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt hmaxa)
    have ha : 0 < a := hb.trans hba
    have hAO : T.tail true a ⊆ O := by
      intro x hx
      have hx' := (T.mem_tail_iff_m28 true ha ha').mp hx
      exact ⟨hattached ((T.mem_tail_iff_m28 true ha₀.1 ha₀.2).mpr
        ⟨hx'.1, ha₀a.trans hx'.2⟩), hx'.1⟩
    have havoid : ∀ x ∈ T.tail true a, (E.inverse x).2 ≠ 1 / 2 := by
      intro x hx heq
      have hxmiddle := (E.mem_middleSphere_iff (hAO hx)).mpr heq
      have hslab := (T.mem_compactSlab_iff hmlo hmhi).mp (hmiddle hxmiddle)
      have hx' := (T.mem_tail_iff_m28 true ha ha').mp hx
      exact (not_lt_of_ge hslab.2.2) (hmhi_a.trans hx'.2)
    let K := W ∩ T.compactSlab b a
    have hK : IsCompact K := hWcompact.inter (T.isCompact_compactSlab hb ha')
    have hKO : K ⊆ O := by
      intro x hx
      exact ⟨hWcap hx.1, T.compactSlab_subset hb ha' hx.2⟩
    obtain ⟨x, hxE, hxK⟩ := E.half_tail_not_subset_compact overlapSide hK hKO
    have hxO := E.tail_subset_m28 overlapSide (by norm_num) (by norm_num) hxE
    have hxW := hcapture hxE
    have hxT : x ∈ T.tail true a := by
      apply (T.mem_tail_iff_m28 true ha ha').mpr
      refine ⟨hxO.2, ?_⟩
      by_contra h
      apply hxK
      exact ⟨hxW, (T.mem_compactSlab_iff hb ha').mpr
        ⟨hxO.2, hbound x hxO, le_of_not_gt h⟩⟩
    exact ⟨a, ha, ha', hfinish ha ha' hAO havoid ⟨x, hxT, hxE⟩⟩

end PoincareConjecture.CapTubeAttachment
