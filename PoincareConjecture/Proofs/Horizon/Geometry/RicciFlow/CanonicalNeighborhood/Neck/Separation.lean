import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

namespace EpsilonNeck

variable {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private lemma coordinate_inverse_axis_mem (x : M) (hx : x ∈ N.carrier) :
    (N.coordinate_inverse x).2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
  (N.coordinate_inverse_mem x hx).2


theorem region_disjoint_of_le {a b c d : ℝ} (hbc : b ≤ c) :
    Disjoint (N.region a b) (N.region c d) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hxc : (N.coordinate_inverse x).2 < c :=
    lt_of_lt_of_le hx.2.2 hbc
  exact (not_lt_of_ge hxc.le) hy.2.1


theorem region_subset_carrier (a b : ℝ) : N.region a b ⊆ N.carrier := by
  intro x hx
  exact hx.1


theorem central_sphere_disjoint_region (a b : ℝ) (ha : b ≤ 0 ∨ 0 ≤ a) :
    Disjoint N.central_sphere (N.region a b) := by
  rw [Set.disjoint_left]
  intro x hxS hxR
  have hx0 : (N.coordinate_inverse x).2 = 0 := by
    rw [N.central_sphere_eq] at hxS
    rcases hxS with ⟨z, hz, hzx⟩
    have hz0 : z.2 = 0 := hz.2
    have hz_eq : z = (z.1, 0) := by
      ext <;> simp [hz0]
    have hzx' := hzx
    rw [hz_eq] at hzx'
    let zd : NeckDomain N.epsilon :=
      (z.1, ⟨z.2, by
        constructor
        · simpa [hz0] using (neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos))
        · simpa [hz0] using (inv_pos.mpr N.epsilon_pos)⟩)
    have hcoord : (N.coordinate zd : M) = x := by
      rw [N.coordinate_map_eq]
      change N.coordinate_map (z.1, (zd.2 : ℝ)) = x
      simpa [zd, hz0] using hzx'
    have hi := congrArg N.coordinate_inverse hcoord
    rw [N.coordinate_inverse_left] at hi
    have hi' := congrArg Prod.snd hi
    calc
      (N.coordinate_inverse x).2 = (zd.2 : ℝ) := hi'.symm
      _ = 0 := by simp [zd, hz0]
  rcases ha with hab | haa
  · change x ∈ N.carrier ∧ a < (N.coordinate_inverse x).2 ∧
      (N.coordinate_inverse x).2 < b at hxR
    rw [hx0] at hxR
    exact (not_lt_of_ge hab) hxR.2.2
  · change x ∈ N.carrier ∧ a < (N.coordinate_inverse x).2 ∧
      (N.coordinate_inverse x).2 < b at hxR
    rw [hx0] at hxR
    exact (not_lt_of_ge haa) hxR.2.1


theorem central_sphere_nonempty : N.central_sphere.Nonempty :=
  ⟨N.center, N.center_on_central_sphere⟩

theorem central_sphere_subset_carrier : N.central_sphere ⊆ N.carrier :=
  N.central_sphere_subset


theorem carrier_subset_region_union_central_union_region :
    N.carrier ⊆ N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere ∪
      N.region 0 N.epsilon⁻¹ := by
  intro x hx
  let a : ℝ := (N.coordinate_inverse x).2
  have ha : a ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact coordinate_inverse_axis_mem N x hx
  rcases lt_trichotomy a 0 with hneg | hzero | hpos
  · exact Or.inl (Or.inl ⟨hx, ha.1, hneg⟩)
  · exact Or.inl (Or.inr (by
    rw [N.central_sphere_eq]
    let z := N.coordinate_inverse x
    have hzero' : z.2 = 0 := by simpa [z] using hzero
    refine ⟨(z.1, 0), ⟨Set.mem_univ _, by simp⟩, ?_⟩
    have hi := congrArg Subtype.val (N.coordinate_inverse_right x hx)
    rw [N.coordinate_map_eq] at hi
    simpa [z, hzero'] using hi)
    )
  · exact Or.inr ⟨hx, hpos, ha.2⟩


theorem carrier_eq_region_union_central_union_region :
    N.carrier = N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere ∪
      N.region 0 N.epsilon⁻¹ := by
  apply Set.Subset.antisymm
  · exact N.carrier_subset_region_union_central_union_region
  · intro x hx
    rcases hx with (hx | hx) | hx
    · exact N.region_subset_carrier _ _ hx
    · exact N.central_sphere_subset_carrier hx
    · exact N.region_subset_carrier _ _ hx



theorem mem_central_sphere_iff (x : M) :
    x ∈ N.central_sphere ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = 0 := by
  constructor
  · intro hx
    have hxc := N.central_sphere_subset hx
    refine ⟨hxc, ?_⟩
    by_contra hzero
    rcases lt_or_gt_of_ne hzero with hneg | hpos
    · exact (Set.disjoint_left.mp
        (N.central_sphere_disjoint_region (-N.epsilon⁻¹) 0 (Or.inl le_rfl))) hx
        ⟨hxc, (N.coordinate_inverse_mem x hxc).2.1, hneg⟩
    · exact (Set.disjoint_left.mp
        (N.central_sphere_disjoint_region 0 N.epsilon⁻¹ (Or.inr le_rfl))) hx
        ⟨hxc, hpos, (N.coordinate_inverse_mem x hxc).2.2⟩
  · rintro ⟨hxc, hzero⟩
    rw [N.central_sphere_eq]
    refine ⟨N.coordinate_inverse x, ⟨Set.mem_univ _, hzero⟩, ?_⟩
    have h := congrArg Subtype.val (N.coordinate_inverse_right x hxc)
    rw [N.coordinate_map_eq] at h
    exact h


theorem isOpen_region (a b : ℝ) : IsOpen (N.region a b) := by
  exact N.coordinate_inverse_smooth.continuousOn.snd.isOpen_inter_preimage
    N.carrier_open isOpen_Ioo


theorem isCompact_coordinate_slab {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    IsCompact (N.coordinate_map '' (Set.univ ×ˢ Set.Icc a b)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  rintro z ⟨_, hz⟩
  exact ⟨Set.mem_univ _, ha.trans_le hz.1, hz.2.trans_lt hb⟩



theorem isCompact_central_sphere : IsCompact N.central_sphere := by
  rw [N.central_sphere_eq, ← Set.Icc_self (0 : ℝ)]
  exact N.isCompact_coordinate_slab
    (neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos)) (inv_pos.mpr N.epsilon_pos)

theorem isClosed_central_sphere : IsClosed N.central_sphere :=
  N.isCompact_central_sphere.isClosed



theorem exists_mem_central_sphere_of_crossing
    {curve : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hcurve : ContinuousOn curve (Set.Icc a b))
    (hcarrier : Set.MapsTo curve (Set.Icc a b) N.carrier)
    (ha : (N.coordinate_inverse (curve a)).2 < 0)
    (hb : 0 < (N.coordinate_inverse (curve b)).2) :
    ∃ t ∈ Set.Ioo a b, curve t ∈ N.central_sphere := by
  have haxis : ContinuousOn (fun t => (N.coordinate_inverse (curve t)).2)
      (Set.Icc a b) :=
    N.coordinate_inverse_smooth.continuousOn.snd.comp hcurve hcarrier
  obtain ⟨t, ht, htzero⟩ := intermediate_value_Icc hab haxis ⟨ha.le, hb.le⟩
  refine ⟨t, ⟨?_, ?_⟩, (N.mem_central_sphere_iff _).mpr ⟨hcarrier ht, htzero⟩⟩
  · exact lt_of_le_of_ne ht.1 (fun h => ha.ne (by simpa [← h] using htzero))
  · exact lt_of_le_of_ne ht.2 (fun h => hb.ne' (by simpa [h] using htzero))

end EpsilonNeck

end PoincareConjecture
