import PoincareConjecture.Proofs.M32.Claim11_32.Extension.StaticMetric
import PoincareConjecture.Proofs.M32.Neck.Spatial













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M32

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
  {e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞}



noncomputable def pullbackEpsilonNeck (K : EpsilonNeck h)
    (he : MetricHomothety g h e 1) (Hcal : MetricHomothetyCalculus g h e 1)
    (D : LeviCivitaData g) : EpsilonNeck g := by
  let coordinate := e.symm ∘ K.coordinate_map
  let eU : (e ⁻¹' K.carrier) ≃ₜ K.carrier := e.toHomeomorph.sets rfl
  have hcoordinate : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-K.epsilon⁻¹) K.epsilon⁻¹) :=
    e.symm.contMDiff.comp_contMDiffOn K.coordinate_map_smooth
  have hscalar : D.scalarCurvature (e.symm K.center) = K.connection.scalarCurvature K.center := by
    simpa using unitHomothety_scalar_eq Hcal D K.connection (e.symm K.center)
  have hcomparison : NeckMetricJetComparison g K.epsilon K.scale coordinate := by
    constructor
    apply roundCylinderClose_congr_axial (B := fun z v w =>
      K.scale⁻¹ ^ 2 * roundCylinderPullback h K.coordinate_map z v w) ?_
      K.metric_comparison.close
    intro z hz v w
    have hdiff := (hcoordinate.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
    have hcomp : e ∘ coordinate = K.coordinate_map := by
      funext y
      exact e.apply_symm_apply _
    have hd : (mfderiv (𝓡 3) (𝓡 3) e (coordinate z)).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) K.coordinate_map z := by
      rw [← mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _) hdiff, hcomp]
    have hv (v : RoundCylinderTangent z) :
        mfderiv (𝓡 3) (𝓡 3) e (coordinate z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) K.coordinate_map z v :=
      congrArg (fun A => A v) hd
    have hm := he (coordinate z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w)
    rw [hv v, hv w, one_mul] at hm
    dsimp only [coordinate, Function.comp_apply] at hm
    rw [e.apply_symm_apply] at hm
    exact congrArg (fun r : ℝ => K.scale⁻¹ ^ 2 * r) hm
  exact {
    epsilon := K.epsilon
    epsilon_pos := K.epsilon_pos
    epsilon_lt_half := K.epsilon_lt_half
    scale := K.scale
    scale_pos := K.scale_pos
    center := e.symm K.center
    connection := D
    scalar_center_pos := hscalar.symm ▸ K.scalar_center_pos
    scale_eq_scalar := by rw [hscalar]; exact K.scale_eq_scalar
    carrier := e ⁻¹' K.carrier
    carrier_open := K.carrier_open.preimage e.continuous
    coordinate := K.coordinate.trans eU.symm
    coordinate_map := coordinate
    coordinate_map_eq := by
      intro z
      change e.symm (K.coordinate z) = e.symm (K.coordinate_map (z.1, z.2))
      rw [K.coordinate_map_eq]
    coordinate_map_smooth := hcoordinate
    coordinate_inverse := K.coordinate_inverse ∘ e
    coordinate_inverse_mem := fun x hx => K.coordinate_inverse_mem (e x) hx
    coordinate_inverse_left := by
      intro z
      change K.coordinate_inverse (e (e.symm (K.coordinate z))) = _
      rw [e.apply_symm_apply]
      exact K.coordinate_inverse_left z
    coordinate_inverse_right := by
      intro x hx
      apply Subtype.ext
      have hi := congrArg Subtype.val (K.coordinate_inverse_right (e x) hx)
      change e.symm ((K.coordinate _) : N) = x
      dsimp only [Function.comp_apply]
      rw [hi, e.symm_apply_apply]
    coordinate_inverse_smooth := K.coordinate_inverse_smooth.comp
      e.contMDiff.contMDiffOn (fun _ hx => hx)
    central_sphere := e ⁻¹' K.central_sphere
    central_sphere_eq := by
      ext x
      change (e x ∈ K.central_sphere) ↔ x ∈ coordinate '' (univ ×ˢ {0})
      rw [K.central_sphere_eq]
      constructor
      · rintro ⟨z, hz, hzx⟩
        refine ⟨z, hz, ?_⟩
        dsimp only [coordinate, Function.comp_apply]
        rw [hzx, e.symm_apply_apply]
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, (e.apply_symm_apply _).symm⟩
    center_on_central_sphere := by
      change e (e.symm K.center) ∈ K.central_sphere
      rw [e.apply_symm_apply]
      exact K.center_on_central_sphere
    central_sphere_subset := fun _ hx => K.central_sphere_subset hx
    metric_comparison := hcomparison }



theorem pullbackEpsilonNeck_region (K : EpsilonNeck h)
    (he : MetricHomothety g h e 1) (Hcal : MetricHomothetyCalculus g h e 1)
    (D : LeviCivitaData g) (a b : ℝ) :
    (pullbackEpsilonNeck K he Hcal D).region a b = e ⁻¹' K.region a b := rfl

end PoincareConjecture.M32
