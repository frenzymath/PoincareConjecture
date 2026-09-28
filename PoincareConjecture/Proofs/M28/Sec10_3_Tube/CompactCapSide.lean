import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapAttachedEnd
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereOrder
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapScalarBand

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CappedTubeCertificate

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_preconnected_compact_cap_side (T : CappedTubeCertificate g) {S : Set M}
    (hS : SmoothSphereIsotopicIn T.tube.carrier S T.tube.cylinder.middleSphere)
    (hcapS : Disjoint T.cap.carrier S) :
    ∃ C : Set M, IsCompact C ∧ IsPreconnected C ∧ C ⊆ T.carrier ∧
      T.cap.carrier ⊆ interior C ∧ S ⊆ C ∧ frontier C ⊆ S := by
  classical
  let U : TopologicalSpace.Opens M := ⟨T.tube.carrier, T.tube.carrier_open⟩
  let E := T.attachment.overlap_model
  let O : Set M := T.cap.carrier ∩ T.tube.carrier
  obtain ⟨φ, lo, hi, hlo, hlohalf, hhalfhi, hhi, hsphere, hfix⟩ :=
    T.tube.cylinder.exists_isotopic_sphere_coordinates (U := U) hS
  let h : M → ℝ := fun x => if T.attachment_side then
    -ambientCylinderSignedHeight φ x else ambientCylinderSignedHeight φ x
  have hcontinuous : ContinuousOn h T.tube.carrier := by
    cases hs : T.attachment_side
    · change ContinuousOn (fun x => if T.attachment_side then
        -ambientCylinderSignedHeight φ x else ambientCylinderSignedHeight φ x) T.tube.carrier
      rw [hs]
      change ContinuousOn (ambientCylinderSignedHeight φ) (U : Set M)
      exact continuousOn_ambientCylinderSignedHeight φ
    · change ContinuousOn (fun x => if T.attachment_side then
        -ambientCylinderSignedHeight φ x else ambientCylinderSignedHeight φ x) T.tube.carrier
      rw [hs]
      change ContinuousOn (fun x => -ambientCylinderSignedHeight φ x) (U : Set M)
      exact (continuousOn_ambientCylinderSignedHeight φ).neg
  have hzero (x : M) (hx : x ∈ T.tube.carrier) : h x = 0 ↔ x ∈ S := by
    simp only [h, ambientCylinderSignedHeight_apply φ hx, cylinderSignedHeight]
    split_ifs <;> simpa only [neg_eq_zero, sub_eq_zero] using hsphere ⟨x, hx⟩
  have hlow (x : M) (hx : x ∈ T.tube.carrier)
      (hheight : (T.tube.cylinder.inverse x).2 < lo) :
      if T.attachment_side then 0 < h x else h x < 0 := by
    have hread := hfix ⟨x, hx⟩ (Or.inl hheight)
    have hh : (T.tube.cylinder.inverse x).2 < 1 / 2 := hheight.trans hlohalf
    cases hs : T.attachment_side <;>
      simp [h, hs,
        ambientCylinderSignedHeight_apply φ hx, cylinderSignedHeight, hread] <;> linarith
  have hhigh (x : M) (hx : x ∈ T.tube.carrier)
      (hheight : hi < (T.tube.cylinder.inverse x).2) :
      if T.attachment_side then h x < 0 else 0 < h x := by
    have hread := hfix ⟨x, hx⟩ (Or.inr hheight)
    have hh : 1 / 2 < (T.tube.cylinder.inverse x).2 := hhalfhi.trans hheight
    cases hs : T.attachment_side <;>
      simp [h, hs,
        ambientCylinderSignedHeight_apply φ hx, cylinderSignedHeight, hread] <;> linarith
  have hST : S ⊆ T.tube.carrier := by
    obtain ⟨H, _, hH, hzero, _⟩ := hS
    rw [← hzero]
    exact (hH 0 (by simp)).2
  obtain ⟨a, ha, ha', hTailCompact, hTailCap⟩ :=
    T.attachment.exists_compact_attached_tail hS hcapS
  have hconn : IsPreconnected O := by
    have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
    let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
    let : ConnectedSpace (Ioo (0 : ℝ) 1) :=
      Subtype.connectedSpace (isConnected_Ioo zero_lt_one)
    let : ConnectedSpace O := E.homeomorph.surjective.connectedSpace E.homeomorph.continuous
    exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have hne : ∀ x ∈ O, h x ≠ 0 := by
    intro x hx heq
    exact disjoint_left.mp hcapS hx.1 ((hzero x hx.2).mp heq)
  have hseed : ∃ x ∈ O, h x < 0 := by
    cases hs : T.attachment_side
    · obtain ⟨x, hx⟩ := T.tube.cylinder.tail_nonempty false (lt_min ha hlo)
        ((min_le_left a lo).trans_lt ha')
      have hx' := (T.tube.cylinder.mem_tail_iff_m28 false (lt_min ha hlo)
        ((min_le_left a lo).trans_lt ha')).mp hx
      have hxa := (T.tube.cylinder.mem_tail_iff_m28 false ha ha').mpr
        ⟨hx'.1, hx'.2.trans_le (min_le_left _ _)⟩
      have hxcap : x ∈ T.cap.carrier := by
        apply hTailCap
        exact subset_closure (by simpa only [hs] using hxa)
      exact ⟨x, ⟨hxcap, hx'.1⟩, by
        simpa [hs] using
          hlow x hx'.1 (hx'.2.trans_le (min_le_right _ _))⟩
    · obtain ⟨x, hx⟩ := T.tube.cylinder.tail_nonempty true
        (ha.trans_le (le_max_left a hi)) (max_lt ha' hhi)
      have hx' := (T.tube.cylinder.mem_tail_iff_m28 true
        (ha.trans_le (le_max_left a hi)) (max_lt ha' hhi)).mp hx
      have hxa := (T.tube.cylinder.mem_tail_iff_m28 true ha ha').mpr
        ⟨hx'.1, (le_max_left _ _).trans_lt hx'.2⟩
      have hxcap : x ∈ T.cap.carrier := by
        apply hTailCap
        exact subset_closure (by simpa only [hs] using hxa)
      exact ⟨x, ⟨hxcap, hx'.1⟩, by
        simpa [hs] using
          hhigh x hx'.1 ((le_max_right _ _).trans_lt hx'.2)⟩
  have hnegative (x : M) (hx : x ∈ O) : h x < 0 :=
    hconn.gt_of_ne (hcontinuous.mono inter_subset_right) hne hseed hx
  let P := T.tube.carrier ∩ h ⁻¹' Ioi (0 : ℝ)
  have hP : IsOpen P := hcontinuous.isOpen_inter_preimage T.tube.carrier_open isOpen_Ioi
  let C := T.carrier \ P
  have hcapC : T.cap.carrier ⊆ C := by
    intro x hx
    refine ⟨T.cap_subset hx, ?_⟩
    intro hxP
    exact (not_lt_of_ge (hnegative x ⟨hx, hxP.1⟩).le) hxP.2
  have hSC : S ⊆ C := by
    intro x hx
    refine ⟨T.tube_subset (hST hx), ?_⟩
    intro hxP
    have hz := (hzero x (hST hx)).mpr hx
    exact (ne_of_gt hxP.2) hz
  obtain ⟨q₀, hq₀, hq₀L, houtside⟩ := T.exists_recut_complement_subset_tube
  obtain ⟨q₁, _, hq₁L, hcaptureTail⟩ :=
    T.cap.exists_recut_capturing_compact hTailCompact hTailCap
  let q := max q₀ q₁
  have hq : 0 < q := hq₀.trans_le (le_max_left _ _)
  have hqL : q < T.cap.epsilon⁻¹ := max_lt hq₀L hq₁L
  let W := closure (T.cap.closed_core ∪ T.cap.end_neck.region (-T.cap.epsilon⁻¹) q)
  obtain ⟨_, hWcompact, hWcap⟩ := T.cap.open_precompact_recut
    ((neg_neg_of_pos (inv_pos.mpr T.cap.epsilon_pos)).trans hq) hqL
  have hrecut₀ : T.cap.closed_core ∪ T.cap.end_neck.region (-T.cap.epsilon⁻¹) q₀ ⊆ W := by
    rintro x (hx | hx)
    · exact subset_closure (Or.inl hx)
    · exact subset_closure (Or.inr ⟨hx.1, hx.2.1, hx.2.2.trans_le (le_max_left _ _)⟩)
  have hTailW : T.tube.cylinder.tail T.attachment_side a ⊆ W := by
    intro x hx
    rcases hcaptureTail (subset_closure hx) with hxcore | hxend
    · exact subset_closure (Or.inl hxcore)
    · exact subset_closure (Or.inr
        ⟨hxend.1, hxend.2.1, hxend.2.2.trans_le (le_max_right _ _)⟩)
  have houtsideW {x : M} (hx : x ∈ T.carrier) (hxW : x ∉ W) : x ∈ T.tube.carrier :=
    houtside ⟨hx, fun hh => hxW (hrecut₀ hh)⟩
  have hcompact : IsCompact C := by
    have hbounded : ∃ l r : ℝ, 0 < l ∧ r < 1 ∧
        C ⊆ W ∪ T.tube.cylinder.compactSlab l r := by
      cases hs : T.attachment_side
      · refine ⟨a, hi, ha, hhi, ?_⟩
        intro x hx
        by_cases hxW : x ∈ W
        · exact Or.inl hxW
        · have hxT := houtsideW hx.1 hxW
          have hax : a ≤ (T.tube.cylinder.inverse x).2 := by
            by_contra hh
            apply hxW
            apply hTailW
            simpa only [hs] using (T.tube.cylinder.mem_tail_iff_m28 false ha ha').mpr
              ⟨hxT, lt_of_not_ge hh⟩
          have hxhi : (T.tube.cylinder.inverse x).2 ≤ hi := by
            by_contra hh
            apply hx.2
            refine ⟨hxT, ?_⟩
            simpa [hs] using hhigh x hxT (lt_of_not_ge hh)
          exact Or.inr ((T.tube.cylinder.mem_compactSlab_iff ha hhi).mpr ⟨hxT, hax, hxhi⟩)
      · refine ⟨lo, a, hlo, ha', ?_⟩
        intro x hx
        by_cases hxW : x ∈ W
        · exact Or.inl hxW
        · have hxT := houtsideW hx.1 hxW
          have hxa : (T.tube.cylinder.inverse x).2 ≤ a := by
            by_contra hh
            apply hxW
            apply hTailW
            simpa only [hs] using (T.tube.cylinder.mem_tail_iff_m28 true ha ha').mpr
              ⟨hxT, lt_of_not_ge hh⟩
          have hlox : lo ≤ (T.tube.cylinder.inverse x).2 := by
            by_contra hh
            apply hx.2
            refine ⟨hxT, ?_⟩
            simpa [hs] using hlow x hxT (lt_of_not_ge hh)
          exact Or.inr ((T.tube.cylinder.mem_compactSlab_iff hlo ha').mpr ⟨hxT, hlox, hxa⟩)
    obtain ⟨l, r, hl, hr, hcapture⟩ := hbounded
    have hbuffer : W ∪ T.tube.cylinder.compactSlab l r ⊆ T.carrier :=
      union_subset (hWcap.trans T.cap_subset)
        ((T.tube.cylinder.compactSlab_subset hl hr).trans T.tube_subset)
    have heq : C = (W ∪ T.tube.cylinder.compactSlab l r) \ P := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨hcapture hx, hx.2⟩
      · intro x hx
        exact ⟨hbuffer hx.1, hx.2⟩
    rw [heq]
    exact (hWcompact.union (T.tube.cylinder.isCompact_compactSlab hl hr)).diff hP
  have hcapInterior : T.cap.carrier ⊆ interior C :=
    interior_maximal hcapC T.cap.carrier_open
  let Half := T.tube.carrier ∩ h ⁻¹' Iic (0 : ℝ)
  have hHalf : IsPreconnected Half := by
    cases hs : T.attachment_side
    · have hpc : IsPreconnected {x : U | cylinderSignedHeight φ x ≤ 0} := by
        rw [← closure_cylinderSignedHeight_negative φ]
        exact (isPreconnected_cylinderSignedHeight_negative φ).closure
      have himage := hpc.image (Subtype.val : U → M) continuous_subtype_val.continuousOn
      convert himage using 1
      ext x
      constructor
      · intro hx
        refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
        have hxheight : h x ≤ 0 := hx.2
        simpa [h, hs, ambientCylinderSignedHeight_apply φ hx.1] using hxheight
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.property, ?_⟩
        change h (x : M) ≤ 0
        simpa [h, hs, ambientCylinderSignedHeight_apply φ x.property] using hx
    · have hpc : IsPreconnected {x : U | 0 ≤ cylinderSignedHeight φ x} := by
        rw [← closure_cylinderSignedHeight_positive φ]
        exact (isPreconnected_cylinderSignedHeight_positive φ).closure
      have himage := hpc.image (Subtype.val : U → M) continuous_subtype_val.continuousOn
      convert himage using 1
      ext x
      constructor
      · intro hx
        refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
        have hxheight : h x ≤ 0 := hx.2
        simpa [h, hs, ambientCylinderSignedHeight_apply φ hx.1] using hxheight
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x.property, ?_⟩
        change h (x : M) ≤ 0
        simpa [h, hs, ambientCylinderSignedHeight_apply φ x.property] using hx
  have hCeq : C = T.cap.carrier ∪ Half := by
    ext x
    constructor
    · intro hx
      by_cases hxcap : x ∈ T.cap.carrier
      · exact Or.inl hxcap
      · have hxT : x ∈ T.tube.carrier := by
          have hxU := hx.1
          rw [T.carrier_eq_union] at hxU
          exact hxU.resolve_left hxcap
        have hn : h x ≤ 0 := le_of_not_gt (fun hh => hx.2 ⟨hxT, hh⟩)
        exact Or.inr ⟨hxT, hn⟩
    · rintro (hxcap | hxHalf)
      · exact hcapC hxcap
      · refine ⟨T.tube_subset hxHalf.1, ?_⟩
        intro hxP
        have hn : h x ≤ 0 := hxHalf.2
        have hp : 0 < h x := hxP.2
        exact (not_lt_of_ge hn) hp
  have hpreconnected : IsPreconnected C := by
    rw [hCeq]
    obtain ⟨x, hxO, hxneg⟩ := hseed
    exact IsPreconnected.union' ⟨x, hxO.1, hxO.2, hxneg.le⟩
      T.cap.isPreconnected_carrier hHalf
  refine ⟨C, hcompact, hpreconnected, sdiff_subset, hcapInterior, hSC, ?_⟩
  intro x hxfront
  have hxC : x ∈ C := hcompact.isClosed.frontier_subset hxfront
  have hxU := hxC.1
  have hxnot : x ∉ interior C := hxfront.2
  by_cases hxcap : x ∈ T.cap.carrier
  · exact False.elim (hxnot (hcapInterior hxcap))
  · have hxT : x ∈ T.tube.carrier := by
      rw [T.carrier_eq_union] at hxU
      exact hxU.resolve_left hxcap
    have hnonpos : h x ≤ 0 := le_of_not_gt (fun hh => hxC.2 ⟨hxT, hh⟩)
    by_cases hz : h x = 0
    · exact (hzero x hxT).mp hz
    · have hlt : h x < 0 := lt_of_le_of_ne hnonpos hz
      let V := T.tube.carrier ∩ h ⁻¹' Iio (0 : ℝ)
      have hV : IsOpen V := hcontinuous.isOpen_inter_preimage T.tube.carrier_open isOpen_Iio
      have hVC : V ⊆ C := by
        intro y hy
        refine ⟨T.tube_subset hy.1, ?_⟩
        intro hyP
        have hn : h y < 0 := hy.2
        have hp : 0 < h y := hyP.2
        exact (not_lt_of_ge hn.le) hp
      exact False.elim (hxnot (interior_maximal hVC hV ⟨hxT, hlt⟩))

theorem exists_compact_cap_side (T : CappedTubeCertificate g) {S : Set M}
    (hS : SmoothSphereIsotopicIn T.tube.carrier S T.tube.cylinder.middleSphere)
    (hcapS : Disjoint T.cap.carrier S) :
    ∃ C : Set M, IsCompact C ∧ C ⊆ T.carrier ∧
      T.cap.carrier ⊆ interior C ∧ S ⊆ C ∧ frontier C ⊆ S := by
  obtain ⟨C, hC, _, hCU, hcap, hS', hfront⟩ :=
    T.exists_preconnected_compact_cap_side hS hcapS
  exact ⟨C, hC, hCU, hcap, hS', hfront⟩

end PoincareConjecture.CappedTubeCertificate
