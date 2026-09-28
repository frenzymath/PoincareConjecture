import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Comparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

def horizon_restrictedCoordinate {δ : ℝ} : OpenPartialHomeomorph RoundCylinderSpace M :=
  N.coordinatePartialHomeomorph.restrOpen (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹) (isOpen_univ.prod isOpen_Ioo)

theorem restrictedCoordinate_source {δ : ℝ} (hεδ : N.epsilon ≤ δ) :
    (N.horizon_restrictedCoordinate (δ := δ)).source = univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ := by
  apply inter_eq_right.mpr
  exact prod_mono subset_rfl (DeepHorn.neckInterval_subset N.epsilon_pos hεδ)

theorem restrictedCoordinate_target {δ : ℝ} :
    (N.horizon_restrictedCoordinate (δ := δ)).target = N.region (-δ⁻¹) δ⁻¹ := by
  ext x
  change (x ∈ N.carrier ∧ N.coordinate_inverse x ∈ univ ×ˢ Ioo (-δ⁻¹) δ⁻¹) ↔ _
  simp only [mem_prod, mem_univ, true_and, region, mem_ofPred_eq, mem_Ioo]

theorem central_sphere_subset_restrictedCoordinate {δ : ℝ} (hδ : 0 < δ) :
    N.central_sphere ⊆ (N.horizon_restrictedCoordinate (δ := δ)).target := by
  rw [N.restrictedCoordinate_target]
  intro x hx
  obtain ⟨z, hz, rfl⟩ := N.central_sphere_eq ▸ hx
  have hz0 : z.2 = 0 := hz.2
  have hzold : z ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    rw [hz0]
    exact ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  refine ⟨N.coordinate_map_mem hzold, ?_⟩
  rw [N.coordinate_inverse_coordinate_map hzold, hz0]
  exact ⟨neg_neg_of_pos (inv_pos.mpr hδ), inv_pos.mpr hδ⟩

variable (h : RiemannianMetric 3 M) (D : LeviCivitaData h)
  {δ : ℝ} (hεδ : N.epsilon ≤ δ) (hδhalf : δ < 1 / 2)
  (hR : 0 < D.scalarCurvature N.center)
  (hclose : RoundCylinderClose δ 0 (fun z v w =>
    D.scalarCurvature N.center * roundCylinderPullback h N.coordinate_map z v w))

def withMetric : EpsilonNeck h := by
  let e := N.horizon_restrictedCoordinate (δ := δ)
  have hsource := N.restrictedCoordinate_source hεδ
  have hδ : 0 < δ := N.epsilon_pos.trans_le hεδ
  have hcentral := N.central_sphere_subset_restrictedCoordinate hδ
  have hpow : ((D.scalarCurvature N.center) ^ (-1 / 2 : ℝ))⁻¹ ^ 2 =
      D.scalarCurvature N.center := by
    rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le]
    norm_num
  exact {
    epsilon := δ
    epsilon_pos := hδ
    epsilon_lt_half := hδhalf
    scale := D.scalarCurvature N.center ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := N.center
    connection := D
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    carrier := e.target
    carrier_open := e.open_target
    coordinate := neckDomainCoordinates e hsource
    coordinate_map := N.coordinate_map
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth := N.coordinate_map_smooth.mono
      (prod_mono subset_rfl (DeepHorn.neckInterval_subset N.epsilon_pos hεδ))
    coordinate_inverse := N.coordinate_inverse
    coordinate_inverse_mem := fun _ hx => neckDomainCoordinates_inverse_mem e hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left e hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right e hsource
    coordinate_inverse_smooth := N.coordinate_inverse_smooth.mono (fun _ hx => hx.1)
    central_sphere := N.central_sphere
    central_sphere_eq := N.central_sphere_eq
    center_on_central_sphere := N.center_on_central_sphere
    central_sphere_subset := hcentral
    metric_comparison := ⟨by simpa only [hpow] using hclose⟩ }

theorem withMetric_carrier :
    (N.withMetric h D hεδ hδhalf hR hclose).carrier = N.region (-δ⁻¹) δ⁻¹ :=
  N.restrictedCoordinate_target

theorem withMetric_region (a b : ℝ) :
    (N.withMetric h D hεδ hδhalf hR hclose).region a b =
      N.region (-δ⁻¹) δ⁻¹ ∩ N.region a b := by
  rw [region, N.withMetric_carrier]
  ext x
  change (x ∈ N.region (-δ⁻¹) δ⁻¹ ∧ a < (N.coordinate_inverse x).2 ∧
    (N.coordinate_inverse x).2 < b) ↔ _
  constructor
  · exact fun hx => ⟨hx.1, hx.1.1, hx.2⟩
  · exact fun hx => ⟨hx.1, hx.2.2⟩

end PoincareConjecture.EpsilonNeck
