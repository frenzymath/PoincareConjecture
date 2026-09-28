import PoincareConjecture.Proofs.M45.Ch12_Standard.StandardNecks
import PoincareConjecture.Proofs.M45.Mathlib.TwoSidedBoundary
import PoincareConjecture.Proofs.M36.NeckCoordinates
import Mathlib.Analysis.Normed.Module.Connected









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem neckRegion_eq_coordinateImage (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) :
    N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b) := by
  ext x
  constructor
  · intro hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, M36.neck_coordinate_inverse N hx.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hdom : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨hz.1, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
    refine ⟨M36.neck_coordinate_mem N z hdom, ?_⟩
    simpa only [M36.neck_inverse_coordinate N z hdom, mem_Ioo] using hz.2



theorem neckRegion_isConnected (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ ≤ a) (hab : a < b) (hb : b ≤ N.epsilon⁻¹) :
    IsConnected (N.region a b) := by
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  have hdom : (univ ×ˢ Ioo a b : Set StandardCylinderSpace) ⊆
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    fun _ hz => ⟨hz.1, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
  rw [neckRegion_eq_coordinateImage N ha hb]
  exact (isConnected_univ.prod (isConnected_Ioo hab)).image _
    (N.coordinate_map_smooth.continuousOn.mono hdom)



theorem neckSphere_subset_closure_region (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ ≤ a) (hab : a < b) (hb : b ≤ N.epsilon⁻¹)
    (ha0 : a ≤ 0) (hb0 : 0 ≤ b) :
    N.central_sphere ⊆ closure (N.region a b) := by
  intro x hx
  rw [N.central_sphere_eq] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hpos := inv_pos.mpr N.epsilon_pos
  have hdom : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    refine ⟨hz.1, ?_⟩
    rw [show z.2 = 0 from hz.2]
    exact ⟨neg_lt_zero.mpr hpos, hpos⟩
  rw [neckRegion_eq_coordinateImage N ha hb]
  apply (M36.neck_coordinate_contMDiffAt N hdom).continuousAt.continuousWithinAt.mem_closure_image
  rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
  exact ⟨mem_univ _, (show z.2 = 0 from hz.2).symm ▸ ⟨ha0, hb0⟩⟩



theorem neckCarrier_subset_halves (N : EpsilonNeck g) :
    N.carrier ⊆ N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere ∪
      N.region 0 N.epsilon⁻¹ := by
  intro x hx
  have hb := (N.coordinate_inverse_mem x hx).2
  rcases lt_trichotomy (N.coordinate_inverse x).2 0 with h | h | h
  · exact Or.inl (Or.inl ⟨hx, hb.1, h⟩)
  · exact Or.inl (Or.inr ((M36.neck_central_iff N).mpr ⟨hx, h⟩))
  · exact Or.inr ⟨hx, h, hb.2⟩



theorem neckHalves_disjoint_sphere (N : EpsilonNeck g) :
    Disjoint (N.region (-N.epsilon⁻¹) 0) N.central_sphere ∧
      Disjoint (N.region 0 N.epsilon⁻¹) N.central_sphere := by
  constructor <;> apply Set.disjoint_left.mpr
  · intro x hx hxB
    have hzero := ((M36.neck_central_iff N).mp hxB).2
    exact (ne_of_lt hx.2.2) hzero
  · intro x hx hxB
    have hzero := ((M36.neck_central_iff N).mp hxB).2
    exact (ne_of_gt hx.2.1) hzero



theorem neck_opposite_sides [PreconnectedSpace M]
    (N : EpsilonNeck g) {K : Set M} (hK : IsClosed K)
    (hinterior : (interior K).Nonempty) (hproper : K ≠ univ)
    (hB : frontier K = N.central_sphere) :
    (N.region (-N.epsilon⁻¹) 0 ⊆ interior K ∧ N.region 0 N.epsilon⁻¹ ⊆ Kᶜ) ∨
      (N.region (-N.epsilon⁻¹) 0 ⊆ Kᶜ ∧ N.region 0 N.epsilon⁻¹ ⊆ interior K) := by
  have hpos := inv_pos.mpr N.epsilon_pos
  have hhalves := neckHalves_disjoint_sphere N
  apply Poincare.Topology.opposite_sides_of_frontier_cover hK N.carrier_open
    hinterior hproper
  · simpa only [hB] using N.central_sphere_subset
  · simpa only [hB] using neckCarrier_subset_halves N
  · exact (neckRegion_isConnected N le_rfl (neg_lt_zero.mpr hpos) hpos.le).isPreconnected
  · exact (neckRegion_isConnected N (neg_nonpos.mpr hpos.le) hpos le_rfl).isPreconnected
  · simpa only [hB] using hhalves.1
  · simpa only [hB] using hhalves.2

end PoincareConjecture.M45
