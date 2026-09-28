import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch
import PoincareConjecture.Proofs.M35.Thm12_28.NeckHomeomorph











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem scalar_scale_inv_sq {Q : ℝ} (hQ : 0 < Q) :
    (Q ^ (-1 / 2 : ℝ))⁻¹ ^ 2 = Q := by
  rw [← Real.rpow_neg hQ.le, ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
  norm_num




noncomputable def transportedStatic (N : EpsilonNeck g)
    (h : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData h)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M StandardCapSpace ∞)
    (hU : N.carrier ⊆ phi.source)
    (hscalar : 0 < D.scalarCurvature (phi N.center))
    (hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.center) * roundCylinderPullback h
        (phi ∘ N.coordinate_map) z v w)) : EpsilonNeck h := by
  let patch := N.transportedStandardPatch phi hU
  refine {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := (D.scalarCurvature (phi N.center)) ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hscalar _
    center := phi N.center
    connection := D
    scalar_center_pos := hscalar
    scale_eq_scalar := rfl
    carrier := patch.carrier
    carrier_open := patch.carrier_open
    coordinate := patch.coordinateHomeomorph
    coordinate_map := patch.coordinate
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth := patch.coordinate_smooth
    coordinate_inverse := patch.inverse
    coordinate_inverse_mem := fun y hy => ⟨mem_univ _, patch.inverse_domain y hy⟩
    coordinate_inverse_left := ?_
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := patch.inverse_smooth
    central_sphere := patch.coordinate '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := ?_
    central_sphere_subset := ?_
    metric_comparison := ?_
  }
  · intro z
    exact patch.coordinate_left_inverse ⟨mem_univ _, z.2.property⟩
  · intro y hy
    apply Subtype.ext
    exact patch.coordinate_right_inverse hy
  · obtain ⟨q, hq⟩ := patch.center_sphere
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, hq⟩
  · rintro y ⟨z, hz, rfl⟩
    rw [← patch.coordinate_image]
    have hz0 : z.2 = 0 := hz.2
    refine ⟨z, ⟨mem_univ _, ?_⟩, rfl⟩
    rw [hz0]
    exact ⟨neg_neg_of_pos patch.length_pos, patch.length_pos⟩
  · refine ⟨?_⟩
    change RoundCylinderClose N.epsilon 0 (fun z v w =>
      ((D.scalarCurvature (phi N.center)) ^ (-1 / 2 : ℝ))⁻¹ ^ 2 *
        roundCylinderPullback h (phi ∘ N.coordinate_map) z v w)
    rw [scalar_scale_inv_sq hscalar]
    exact hclose



theorem transportedStatic_carrier (N : EpsilonNeck g)
    (h : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData h)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M StandardCapSpace ∞)
    (hU : N.carrier ⊆ phi.source)
    (hscalar : 0 < D.scalarCurvature (phi N.center))
    (hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.center) * roundCylinderPullback h
        (phi ∘ N.coordinate_map) z v w)) :
    (N.transportedStatic h D phi hU hscalar hclose).carrier = phi '' N.carrier := by
  change (N.transportedStandardPatch phi hU).carrier = _
  rw [← (N.transportedStandardPatch phi hU).coordinate_image]
  change (phi ∘ N.coordinate_map) '' (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) = _
  have hcoordinate : N.coordinate_map '' (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) =
      N.carrier := N.coordinatePartialDiffeomorph.toOpenPartialHomeomorph.image_source_eq_target
  rw [image_comp, hcoordinate]



theorem transportedStatic_central_sphere (N : EpsilonNeck g)
    (h : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData h)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M StandardCapSpace ∞)
    (hU : N.carrier ⊆ phi.source)
    (hscalar : 0 < D.scalarCurvature (phi N.center))
    (hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.center) * roundCylinderPullback h
        (phi ∘ N.coordinate_map) z v w)) :
    (N.transportedStatic h D phi hU hscalar hclose).central_sphere = phi '' N.central_sphere := by
  change (phi ∘ N.coordinate_map) '' (univ ×ˢ ({0} : Set ℝ)) = _
  rw [image_comp, N.central_sphere_eq]



theorem transportedStatic_region (N : EpsilonNeck g)
    (h : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData h)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M StandardCapSpace ∞)
    (hU : N.carrier ⊆ phi.source)
    (hscalar : 0 < D.scalarCurvature (phi N.center))
    (hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      D.scalarCurvature (phi N.center) * roundCylinderPullback h
        (phi ∘ N.coordinate_map) z v w)) (a b : ℝ) :
    (N.transportedStatic h D phi hU hscalar hclose).region a b = phi '' N.region a b := by
  ext y
  change (y ∈ (N.transportedStatic h D phi hU hscalar hclose).carrier ∧
    a < (N.coordinate_inverse (phi.invFun y)).2 ∧
      (N.coordinate_inverse (phi.invFun y)).2 < b) ↔ y ∈ phi '' N.region a b
  rw [N.transportedStatic_carrier h D phi hU hscalar hclose]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ha, hb⟩
    have hleft : phi.invFun (phi z) = z := phi.left_inv (hU hz)
    rw [hleft] at ha hb
    exact ⟨z, ⟨hz, ha, hb⟩, rfl⟩
  · rintro ⟨z, ⟨hz, ha, hb⟩, rfl⟩
    have hleft : phi.invFun (phi z) = z := phi.left_inv (hU hz)
    exact ⟨⟨z, hz, rfl⟩, hleft.symm ▸ ha, hleft.symm ▸ hb⟩

end PoincareConjecture.EpsilonNeck
