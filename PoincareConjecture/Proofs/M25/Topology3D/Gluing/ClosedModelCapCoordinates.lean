import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapData










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D.ClosedModelCapData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} (C : ClosedModelCapData g)


abbrev coordinate_map : RoundCylinderSpace → M := C.end_chart


abbrev coordinate_inverse : M → RoundCylinderSpace := C.end_chart.symm


def cylinderDomain : Set RoundCylinderSpace := univ ×ˢ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹


abbrev coordinatePartialHomeomorph : OpenPartialHomeomorph RoundCylinderSpace M := C.end_chart


def region (a b : ℝ) : Set M :=
  {x | x ∈ C.end_chart.target ∧ (C.coordinate_inverse x).2 ∈ Ioo a b}


noncomputable def endCenter : M := by
  have hq := (NormedSpace.sphere_nonempty (E := E3) (x := 0) (r := 1)).mpr
    (by norm_num)
  exact C.coordinate_map (⟨Classical.choose hq, Classical.choose_spec hq⟩, 0)


theorem cylinderDomain_open : IsOpen C.cylinderDomain := isOpen_univ.prod isOpen_Ioo


theorem coordinate_map_mem {z : RoundCylinderSpace} (hz : z ∈ C.cylinderDomain) :
    C.coordinate_map z ∈ C.end_chart.target :=
  C.end_chart.map_source (C.end_chart_source.symm ▸ hz)


theorem coordinate_inverse_mem (x : M) (hx : x ∈ C.end_chart.target) :
    C.coordinate_inverse x ∈ C.cylinderDomain := by
  rw [cylinderDomain, ← C.end_chart_source]
  exact C.end_chart.map_target hx


theorem coordinate_inverse_coordinate_map {z : RoundCylinderSpace}
    (hz : z ∈ C.cylinderDomain) : C.coordinate_inverse (C.coordinate_map z) = z :=
  C.end_chart.left_inv (C.end_chart_source.symm ▸ hz)


theorem coordinate_inverse_map (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    C.coordinate_inverse (C.coordinate_map z) = z :=
  C.coordinate_inverse_coordinate_map ⟨mem_univ _, hz⟩


theorem coordinate_map_coordinate_inverse {x : M} (hx : x ∈ C.end_chart.target) :
    C.coordinate_map (C.coordinate_inverse x) = x := C.end_chart.right_inv hx


theorem coordinate_map_inverse {x : M} (hx : x ∈ C.end_chart.target) :
    C.coordinate_map (C.coordinate_inverse x) = x := C.coordinate_map_coordinate_inverse hx


theorem coordinate_map_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ C.coordinate_map C.cylinderDomain := by
  rw [cylinderDomain, ← C.end_chart_source]
  exact C.end_chart_smooth


theorem coordinate_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      C.coordinate_inverse C.end_chart.target := C.end_chart_inverse_smooth


theorem region_eq_image {a b : ℝ} (ha : -C.epsilon⁻¹ ≤ a) (hb : b ≤ C.epsilon⁻¹) :
    C.region a b = C.coordinate_map '' (univ ×ˢ Ioo a b) := by
  ext x
  constructor
  · intro hx
    exact ⟨C.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, C.coordinate_map_inverse hx.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hzs : z ∈ C.cylinderDomain :=
      ⟨mem_univ _, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
    refine ⟨C.coordinate_map_mem hzs, ?_⟩
    rw [C.coordinate_inverse_coordinate_map hzs]
    exact hz.2


theorem region_upper_eq_cylinderTail {t : ℝ}
    (ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    C.region t C.epsilon⁻¹ = C.end_chart.cylinderTail C.epsilon⁻¹ t :=
  C.region_eq_image ht.1.le le_rfl


theorem isCompact_end_neck_lower_cut {t : ℝ}
    (ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    IsCompact (C.carrier \ C.region t C.epsilon⁻¹) := by
  rw [C.region_upper_eq_cylinderTail ht]
  exact C.compact_tail_complement t ht



theorem end_neck_lower_cut_topology {t : ℝ}
    (ht : t ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    let L := C.epsilon⁻¹
    let Kt := C.carrier \ C.region t L
    let Ut := C.closed_core ∪ C.region (-L) t
    let St := C.coordinate_map '' (univ ×ˢ ({t} : Set ℝ))
    Kt ⊆ C.carrier ∧ IsOpen Ut ∧ closure Ut = Kt ∧ interior Kt = Ut ∧
      frontier Ut = St ∧ frontier Kt = St ∧
      frontier C.carrier ⊆ closure (C.region t L) := by
  dsimp only
  rw [C.region_upper_eq_cylinderTail ht, C.region_eq_image le_rfl ht.2.le]
  exact C.cut_topology t ht

end PoincareConjecture.M25.Topology3D.ClosedModelCapData
