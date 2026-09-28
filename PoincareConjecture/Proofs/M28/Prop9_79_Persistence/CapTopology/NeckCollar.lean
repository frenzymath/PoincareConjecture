import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem isPreconnected_region (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) :
    IsPreconnected (N.region a b) := by
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  rw [N.region_eq_image_m28 ha hb]
  apply (isPreconnected_univ.prod isPreconnected_Ioo).image
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩

theorem mem_central_sphere_iff_of_mem_carrier (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier) :
    x ∈ N.central_sphere ↔ (N.coordinate_inverse x).2 = 0 := by
  rw [N.central_sphere_eq]
  constructor
  · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs0 : s = 0 := hs
    subst s
    have hpos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    exact congrArg Prod.snd
      (N.coordinate_inverse_coordinate_map_of_axial (q, 0) ⟨neg_neg_of_pos hpos, hpos⟩)
  · intro hzero
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hzero⟩,
      N.coordinate_map_coordinate_inverse hx⟩

theorem central_sphere_subset_region (N : EpsilonNeck g) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) : N.central_sphere ⊆ N.region a b := by
  intro x hx
  have hxC := N.central_sphere_subset hx
  have hzero := (N.mem_central_sphere_iff_of_mem_carrier hxC).mp hx
  exact ⟨hxC, by simpa only [hzero] using And.intro ha hb⟩

theorem region_split_zero (N : EpsilonNeck g) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) :
    N.region a b = N.region a 0 ∪ N.central_sphere ∪ N.region 0 b := by
  ext x
  constructor
  · intro hx
    rcases lt_trichotomy (N.coordinate_inverse x).2 0 with hneg | hzero | hpos
    · exact Or.inl (Or.inl ⟨hx.1, hx.2.1, hneg⟩)
    · exact Or.inl (Or.inr ((N.mem_central_sphere_iff_of_mem_carrier hx.1).mpr hzero))
    · exact Or.inr ⟨hx.1, hpos, hx.2.2⟩
  · rintro ((hx | hx) | hx)
    · exact ⟨hx.1, hx.2.1, hx.2.2.trans hb⟩
    · exact N.central_sphere_subset_region ha hb hx
    · exact ⟨hx.1, ha.trans hx.2.1, hx.2.2⟩

theorem exists_region_zero_subset (N : EpsilonNeck g) {U : Set M}
    (hU : IsOpen U) (hS : N.central_sphere ⊆ U) :
    ∃ a b : ℝ, -N.epsilon⁻¹ < a ∧ a < 0 ∧ 0 < b ∧ b < N.epsilon⁻¹ ∧
      N.region a b ⊆ U := by
  have hpos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let O : Set (UnitTwoSphere × ℝ) :=
    (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∩ N.coordinate_map ⁻¹' U
  have hO : IsOpen O := N.coordinate_map_smooth.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod isOpen_Ioo) hU
  have hSO : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ O := by
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    refine ⟨⟨mem_univ _, ?_⟩, hS ?_⟩
    · rw [hz0]
      exact ⟨neg_neg_of_pos hpos, hpos⟩
    · rw [N.central_sphere_eq]
      exact mem_image_of_mem _ hz
  obtain ⟨s, t, _, ht, hst, hzt, hprod⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hO hSO
  have hneigh : t ∩ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∈ 𝓝 (0 : ℝ) :=
    Filter.inter_mem (ht.mem_nhds (hzt rfl))
      (Ioo_mem_nhds (neg_neg_of_pos hpos) hpos)
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hneigh
  have ha : a / 2 ∈ Ioo a b := ⟨by linarith [hab.1], by linarith [hab.1, hab.2]⟩
  have hb : b / 2 ∈ Ioo a b := ⟨by linarith [hab.1, hab.2], by linarith [hab.2]⟩
  refine ⟨a / 2, b / 2, (hsub ha).2.1, by linarith [hab.1],
    by linarith [hab.2], (hsub hb).2.2, ?_⟩
  intro x hx
  have hz : N.coordinate_inverse x ∈ O := hprod
    ⟨hst (mem_univ _), (hsub ⟨ha.1.trans hx.2.1, hx.2.2.trans hb.2⟩).1⟩
  simpa only [mem_preimage, N.coordinate_map_coordinate_inverse hx.1] using hz.2

end PoincareConjecture.EpsilonNeck
