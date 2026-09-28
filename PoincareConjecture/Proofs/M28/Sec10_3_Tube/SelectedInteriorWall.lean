import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereOrder
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {X : Set M}

theorem exists_selected_chain_tail_above_cylinder_level
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (R : M → ℝ) (hR : ContinuousOn R T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        R y ≤ 2 * R z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < R x)
    {c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1) :
    ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ i ∈ T.chain.shape.active, ∀ y ∈ (T.chain.neck i).carrier,
        d < (A.inverse y).2 → (T.chain.neck i).carrier ⊆ A.tail true c := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hsection := A.isCompact_compactSlab hc0 hc1
  obtain ⟨B, hB⟩ := hsection.bddAbove_image
    (hR.mono (A.compactSlab_subset hc0 hc1))
  obtain ⟨d, hd, hd1, hhigh⟩ := hdiverge (2 * B)
  refine ⟨max c d, lt_max_of_lt_left hc, max_lt hc1 hd1, ?_⟩
  intro i hi y hyN hy
  have hNV : (T.chain.neck i).carrier ⊆ T.carrier := by
    rw [T.carrier_eq_chain_union]
    exact subset_iUnion_of_subset ⟨i, hi⟩ Subset.rfl
  have hyc : c < (A.inverse y).2 := (le_max_left _ _).trans_lt hy
  have hyR : 2 * B < R y :=
    hhigh y (hNV hyN) ((le_max_right _ _).trans_lt hy)
  have hheight : ContinuousOn (fun x => (A.inverse x).2) (T.chain.neck i).carrier :=
    (continuous_snd.comp_continuousOn A.inverse_smooth.continuousOn).mono hNV
  have havoid : ∀ z ∈ (T.chain.neck i).carrier, (A.inverse z).2 ≠ c := by
    intro z hz heq
    have hzsection : z ∈ A.compactSlab c c :=
      (A.mem_compactSlab_iff hc0 hc1).mpr ⟨hNV hz, heq.ge, heq.le⟩
    have hzB : R z ≤ B := hB (mem_image_of_mem R hzsection)
    have hratioz := hratio i hi y hyN z hz
    linarith
  intro z hz
  apply (A.mem_tail_iff_m28 true hc0 hc1).mpr
  exact ⟨hNV hz, (T.chain.neck i).isConnected_carrier.isPreconnected.lt_of_ne
    hheight havoid ⟨y, hyN, hyc⟩ hz⟩

theorem exists_selected_chain_neck_above_cylinder_level
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (R : M → ℝ) (hR : ContinuousOn R T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        R y ≤ 2 * R z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < R x)
    {c : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1) :
    ∃ i ∈ T.chain.shape.active, (T.chain.neck i).carrier ⊆ A.tail true c := by
  obtain ⟨d, hd, hd1, htail⟩ :=
    exists_selected_chain_tail_above_cylinder_level T A R hR hratio hdiverge hc hc1
  have hd0 : 0 < d := lt_trans (by norm_num) hd
  obtain ⟨y, hy⟩ := A.tail_nonempty true hd0 hd1
  have hyread := (A.mem_tail_iff_m28 true hd0 hd1).mp hy
  obtain ⟨i, hyN⟩ := mem_iUnion.mp (T.carrier_eq_chain_union ▸ hyread.1)
  exact ⟨i.1, i.2, htail i.1 i.2 y hyN hyread.2⟩

omit [T2Space M] in

theorem exists_fixed_positive_side_above_cylinder_level
    {V : TopologicalSpace.Opens M} (A : OpenCylinderModel (V : Set M))
    (N : EpsilonNeck g) {lambda : ℝ}
    (hlambda : 1 / 2 < lambda) (hlambda1 : lambda < 1)
    (hN : N.carrier ⊆ A.tail true lambda)
    (hisotopy : SmoothSphereIsotopicIn (V : Set M) N.central_sphere A.middleSphere) :
    ∃ (phi : V ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) (a b : ℝ),
      0 < a ∧ a < 1 / 2 ∧ 1 / 2 < b ∧ b < 1 ∧
      (∀ x ∈ V, ambientCylinderSignedHeight phi x = 0 ↔ x ∈ N.central_sphere) ∧
      (∀ x ∈ V, (A.inverse x).2 < a ∨ b < (A.inverse x).2 →
        ambientCylinderSignedHeight phi x = (A.inverse x).2 - 1 / 2) ∧
      ∀ x ∈ V, 0 ≤ ambientCylinderSignedHeight phi x → lambda ≤ (A.inverse x).2 := by
  obtain ⟨phi, a, b, ha, hahalf, hbhalf, hb, hzero, hread⟩ :=
    A.exists_isotopic_sphere_coordinates hisotopy
  have hlambda0 : 0 < lambda := lt_trans (by norm_num) hlambda
  have hz (x : M) (hx : x ∈ V) :
      ambientCylinderSignedHeight phi x = 0 ↔ x ∈ N.central_sphere := by
    rw [ambientCylinderSignedHeight_apply phi hx]
    exact sub_eq_zero.trans (hzero ⟨x, hx⟩)
  have ht (x : M) (hx : x ∈ V)
      (hh : (A.inverse x).2 < a ∨ b < (A.inverse x).2) :
      ambientCylinderSignedHeight phi x = (A.inverse x).2 - 1 / 2 := by
    rw [ambientCylinderSignedHeight_apply phi hx]
    change ((phi ⟨x, hx⟩).2 : ℝ) - 1 / 2 = _
    rw [hread ⟨x, hx⟩ hh]
  have hLsub : A.tail false lambda ⊆ (V : Set M) :=
    A.tail_subset_m28 false hlambda0 hlambda1
  have havoid : ∀ x ∈ A.tail false lambda, ambientCylinderSignedHeight phi x ≠ 0 := by
    intro x hx heq
    have hxlow := (A.mem_tail_iff_m28 false hlambda0 hlambda1).mp hx
    have hxhigh := (A.mem_tail_iff_m28 true hlambda0 hlambda1).mp
      (hN (N.central_sphere_subset ((hz x hxlow.1).mp heq)))
    exact (not_lt_of_ge hxhigh.2.le) hxlow.2
  obtain ⟨y, hy⟩ := A.tail_nonempty false (lt_min ha hlambda0)
    ((min_le_left _ _).trans_lt (hahalf.trans (by norm_num)))
  have hyread := (A.mem_tail_iff_m28 false (lt_min ha hlambda0)
    ((min_le_left _ _).trans_lt (hahalf.trans (by norm_num)))).mp hy
  have hyL : y ∈ A.tail false lambda :=
    (A.mem_tail_iff_m28 false hlambda0 hlambda1).mpr
      ⟨hyread.1, hyread.2.trans_le (min_le_right _ _)⟩
  have hyneg : ambientCylinderSignedHeight phi y < 0 := by
    rw [ht y hyread.1 (Or.inl (hyread.2.trans_le (min_le_left _ _)))]
    exact sub_neg.mpr ((hyread.2.trans_le (min_le_left _ _)).trans hahalf)
  have hnegative : ∀ x ∈ A.tail false lambda, ambientCylinderSignedHeight phi x < 0 :=
    fun _ hx => (A.isPreconnected_tail false hlambda0 hlambda1).gt_of_ne
      ((continuousOn_ambientCylinderSignedHeight phi).mono hLsub)
      havoid ⟨y, hyL, hyneg⟩ hx
  refine ⟨phi, a, b, ha, hahalf, hbhalf, hb, hz, ht, ?_⟩
  intro x hx hpos
  apply le_of_not_gt
  intro hlow
  exact (not_lt_of_ge hpos)
    (hnegative x ((A.mem_tail_iff_m28 false hlambda0 hlambda1).mpr ⟨hx, hlow⟩))

end PoincareConjecture.M28
