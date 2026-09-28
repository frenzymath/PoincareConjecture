import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.OpenRecut
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

theorem coordinate_mem_m28 (T : OpenCylinderModel U)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (0 : ℝ) 1) :
    T.coordinate z ∈ U := by
  simpa only [T.coordinate_eq] using
    (T.homeomorph (z.1, ⟨z.2, hz⟩)).property

def compactSlab (T : OpenCylinderModel U) (a b : ℝ) : Set M :=
  T.coordinate '' (univ ×ˢ Icc a b)

theorem isCompact_compactSlab (T : OpenCylinderModel U) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) : IsCompact (T.compactSlab a b) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply T.coordinate_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

theorem compactSlab_subset (T : OpenCylinderModel U) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) : T.compactSlab a b ⊆ U := by
  rintro x ⟨z, hz, rfl⟩
  exact T.coordinate_mem_m28 ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

theorem mem_compactSlab_iff (T : OpenCylinderModel U) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) {x : M} :
    x ∈ T.compactSlab a b ↔ x ∈ U ∧ (T.inverse x).2 ∈ Icc a b := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
      ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
    exact ⟨T.coordinate_mem_m28 hz'.2, by rw [T.left_inverse hz']; exact hz.2⟩
  · rintro ⟨hx, hh⟩
    exact ⟨T.inverse x, ⟨mem_univ _, hh⟩, T.right_inverse hx⟩

theorem exists_compactSlab_capturing (T : OpenCylinderModel U)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ K ⊆ T.compactSlab a b := by
  have hc : ContinuousOn (fun x => (T.inverse x).2) K :=
    (continuous_snd.comp_continuousOn T.inverse_smooth.continuousOn).mono hKU
  obtain ⟨lo, hlo, hlow⟩ := hK.exists_forall_le' hc
    (fun x hx => (T.inverse_mem x (hKU hx)).2.1)
  obtain ⟨margin, hmargin, hhigh⟩ := hK.exists_forall_le'
    (continuousOn_const.sub hc)
    (fun x hx => sub_pos.mpr (T.inverse_mem x (hKU hx)).2.2)
  have hhi : 1 - margin < (1 : ℝ) := by linarith
  have hhigh' (x : M) (hx : x ∈ K) : (T.inverse x).2 ≤ 1 - margin := by
    have hh := hhigh x hx
    change margin ≤ 1 - (T.inverse x).2 at hh
    linarith
  obtain ⟨a, ha, halow⟩ := exists_between (lt_min hlo (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨b, hhib, hb⟩ := exists_between (max_lt hhi (by norm_num : (1 / 2 : ℝ) < 1))
  have hab : a < b :=
    (halow.trans_le (min_le_right _ _)).trans
      ((le_max_right _ _).trans_lt hhib)
  refine ⟨a, b, ha, hab, hb, ?_⟩
  intro x hx
  exact (T.mem_compactSlab_iff ha hb).mpr ⟨hKU hx,
    (halow.trans_le (min_le_left _ _)).le.trans (hlow x hx),
    (hhigh' x hx).trans ((le_max_left _ _).trans_lt hhib).le⟩

theorem exists_compactSlab_capturing_path (T : OpenCylinderModel U)
    {γ : ℝ → M} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγU : MapsTo γ (Icc (0 : ℝ) 1) U) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      MapsTo γ (Icc (0 : ℝ) 1) (T.compactSlab a b) := by
  obtain ⟨a, b, ha, hab, hb, hcapture⟩ :=
    T.exists_compactSlab_capturing (isCompact_Icc.image_of_continuousOn hγ)
      (by rintro x ⟨t, ht, rfl⟩; exact hγU ht)
  exact ⟨a, b, ha, hab, hb, fun t ht => hcapture ⟨t, ht, rfl⟩⟩

theorem path_crosses_coordinate_sphere (T : OpenCylinderModel U)
    {γ : ℝ → M} {a b c : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hγU : MapsTo γ (Icc a b) U)
    (hc : c ∈ Icc (T.inverse (γ a)).2 (T.inverse (γ b)).2) :
    ∃ t ∈ Icc a b, γ t ∈ T.coordinate '' (univ ×ˢ ({c} : Set ℝ)) := by
  have hheight : ContinuousOn (fun t => (T.inverse (γ t)).2) (Icc a b) :=
    continuous_snd.comp_continuousOn
      (T.inverse_smooth.continuousOn.comp hγ hγU)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hab hheight hc
  exact ⟨t, ht, T.inverse (γ t), ⟨mem_univ _, heq⟩,
    T.right_inverse (hγU ht)⟩

end PoincareConjecture.OpenCylinderModel

namespace PoincareConjecture.CappedTubeCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem isCompact_closedCore_union_slab (T : CappedTubeCertificate g)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    IsCompact (T.cap.closed_core ∪ T.tube.cylinder.compactSlab a b) ∧
      T.cap.closed_core ∪ T.tube.cylinder.compactSlab a b ⊆ T.carrier := by
  refine ⟨T.cap.closed_core_compact.union
    (T.tube.cylinder.isCompact_compactSlab ha hb), ?_⟩
  apply union_subset
  · have hcore : T.cap.closed_core ⊆ T.cap.carrier := by
      rw [T.cap.closed_core_eq_complement_end]
      exact sdiff_subset
    exact hcore.trans T.cap_subset
  · exact (T.tube.cylinder.compactSlab_subset ha hb).trans T.tube_subset

omit [T2Space M] in

theorem exists_recut_complement_subset_tube (T : CappedTubeCertificate g) :
    ∃ b : ℝ, 0 < b ∧ b < T.cap.epsilon⁻¹ ∧
      T.carrier \ (T.cap.closed_core ∪
        T.cap.end_neck.region (-T.cap.epsilon⁻¹) b) ⊆ T.tube.carrier := by
  obtain ⟨s, hs, htail⟩ := T.attachment.cap_tail
  obtain ⟨b, hsb, hb⟩ := exists_between hs.2
  refine ⟨b, hs.1.trans hsb, hb, ?_⟩
  intro x hx
  have hxunion : x ∈ T.cap.carrier ∪ T.tube.carrier :=
    T.carrier_eq_union ▸ hx.1
  rcases hxunion with hxcap | hxtube
  · have hxend : x ∈ T.cap.end_neck.carrier := by
      by_contra hxend
      apply hx.2
      apply Or.inl
      rw [T.cap.closed_core_eq_complement_end]
      exact ⟨hxcap, hxend⟩
    have hlow : -T.cap.epsilon⁻¹ < (T.cap.end_neck.coordinate_inverse x).2 := by
      simpa only [T.cap.end_neck_epsilon] using
        (T.cap.end_neck.coordinate_inverse_mem x hxend).2.1
    have hhigh : (T.cap.end_neck.coordinate_inverse x).2 < T.cap.epsilon⁻¹ := by
      simpa only [T.cap.end_neck_epsilon] using
        (T.cap.end_neck.coordinate_inverse_mem x hxend).2.2
    have hbcoord : b ≤ (T.cap.end_neck.coordinate_inverse x).2 := by
      by_contra h
      exact hx.2 (Or.inr ⟨hxend, hlow, lt_of_not_ge h⟩)
    exact htail ⟨hxend, hsb.trans_le hbcoord, hhigh⟩
  · exact hxtube

theorem exists_compact_recut_union_slab_capturing (T : CappedTubeCertificate g)
    {K : Set M} (hK : IsCompact K) (hKT : K ⊆ T.carrier) :
    ∃ b a c : ℝ, 0 < b ∧ b < T.cap.epsilon⁻¹ ∧
      0 < a ∧ a < c ∧ c < 1 ∧
      IsCompact (closure (T.cap.closed_core ∪
        T.cap.end_neck.region (-T.cap.epsilon⁻¹) b) ∪
          T.tube.cylinder.compactSlab a c) ∧
      (closure (T.cap.closed_core ∪
        T.cap.end_neck.region (-T.cap.epsilon⁻¹) b) ∪
          T.tube.cylinder.compactSlab a c) ⊆ T.carrier ∧
      K ⊆ closure (T.cap.closed_core ∪
        T.cap.end_neck.region (-T.cap.epsilon⁻¹) b) ∪
          T.tube.cylinder.compactSlab a c := by
  obtain ⟨b, hb, hbA, houtside⟩ := T.exists_recut_complement_subset_tube
  have hA : 0 < T.cap.epsilon⁻¹ := inv_pos.mpr T.cap.epsilon_pos
  have hneg : -T.cap.epsilon⁻¹ < b := (neg_neg_of_pos hA).trans hb
  let W : Set M := T.cap.closed_core ∪
    T.cap.end_neck.region (-T.cap.epsilon⁻¹) b
  obtain ⟨hWopen, hWcompact, hWcap⟩ := T.cap.open_precompact_recut hneg hbA
  have hrest : K \ W ⊆ T.tube.carrier := by
    intro x hx
    exact houtside ⟨hKT hx.1, hx.2⟩
  obtain ⟨a, c, ha, hac, hc, hslab⟩ :=
    T.tube.cylinder.exists_compactSlab_capturing (hK.diff hWopen) hrest
  refine ⟨b, a, c, hb, hbA, ha, hac, hc,
    hWcompact.union (T.tube.cylinder.isCompact_compactSlab ha hc),
    union_subset (hWcap.trans T.cap_subset)
      ((T.tube.cylinder.compactSlab_subset ha hc).trans T.tube_subset), ?_⟩
  intro x hx
  by_cases hxW : x ∈ W
  · exact Or.inl (subset_closure hxW)
  · exact Or.inr (hslab ⟨hx, hxW⟩)

end PoincareConjecture.CappedTubeCertificate
