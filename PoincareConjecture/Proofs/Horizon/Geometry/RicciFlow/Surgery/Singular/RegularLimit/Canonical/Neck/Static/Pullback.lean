import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

noncomputable section

namespace PoincareConjecture.EpsilonNeck

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
  [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
  {g : RiemannianMetric 3 X} {h : RiemannianMetric 3 Y}
  (N : EpsilonNeck h) (D : LeviCivitaData g)
  {e : X → Y} {k : Y → X}
  (he : Topology.IsOpenEmbedding e) (hes : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
  (hks : ContMDiffOn (𝓡 3) (𝓡 3) ∞ k N.carrier)
  (hleft : Function.LeftInverse k e) (hright : LeftInvOn e k N.carrier)
  (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
    h.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) = g.inner x v w)

def pullbackOpenCarrierHomeomorph : (e ⁻¹' N.carrier) ≃ₜ N.carrier :=
  he.isEmbedding.homeomorphOfSubsetRange (fun y hy => ⟨k y, hright hy⟩)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X] in
theorem pullbackOpenCarrierHomeomorph_symm (y : N.carrier) :
    ((N.pullbackOpenCarrierHomeomorph he hright).symm y : X) = k y := by
  apply he.injective
  rw [hright y.property]
  exact congrArg Subtype.val ((N.pullbackOpenCarrierHomeomorph he hright).apply_symm_apply y)

include hks in
omit [IsManifold (𝓡 3) ∞ X] in
theorem pullbackOpen_coordinate_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (k ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
  hks.comp N.coordinate_map_smooth (fun _ hz => N.coordinate_map_mem hz)

include hes hks hright hmetric in
theorem pullbackOpen_metric (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v w : RoundCylinderTangent z) :
    roundCylinderPullback g (k ∘ N.coordinate_map) z v w =
      roundCylinderPullback h N.coordinate_map z v w := by
  let f := k ∘ N.coordinate_map
  have hz' : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨mem_univ _, hz⟩
  have hf := ((N.pullbackOpen_coordinate_smooth hks).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz')).mdifferentiableAt (by simp)
  have hlocal : e ∘ f =ᶠ[𝓝 z] N.coordinate_map := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hz'] with y hy
    exact hright (N.coordinate_map_mem hy)
  have hd := (mfderiv_comp z ((hes _).mdifferentiableAt (by simp)) hf).symm.trans hlocal.mfderiv_eq
  unfold roundCylinderPullback
  rw [← hmetric]
  have hv (a : RoundCylinderTangent z) :
      mfderiv (𝓡 3) (𝓡 3) e (f z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z a) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z a :=
    congrArg (fun A => A a) hd
  rw [hv v, hv w]
  exact congrArg (fun y : Y => h.inner y
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w)) hlocal.self_of_nhds

def pullbackOpen : EpsilonNeck g := by
  let eU := N.pullbackOpenCarrierHomeomorph he hright
  have hcenter : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have hscalar : D.scalarCurvature (k N.center) = N.connection.scalarCurvature N.center := by
    have hh := D.scalarCurvature_eq_of_local_isometry N.connection isOpen_univ
      hes.contMDiffOn (fun x _ v w => (hmetric x v w).symm) (mem_univ (k N.center))
    rw [hright hcenter] at hh
    exact hh
  exact {
    epsilon := N.epsilon
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scale := N.scale
    scale_pos := N.scale_pos
    center := k N.center
    connection := D
    scalar_center_pos := hscalar.symm ▸ N.scalar_center_pos
    scale_eq_scalar := by rw [hscalar]; exact N.scale_eq_scalar
    carrier := e ⁻¹' N.carrier
    carrier_open := N.carrier_open.preimage he.continuous
    coordinate := N.coordinate.trans eU.symm
    coordinate_map := k ∘ N.coordinate_map
    coordinate_map_eq := by
      intro z
      change (eU.symm (N.coordinate z) : X) = k (N.coordinate_map (z.1, z.2))
      rw [N.pullbackOpenCarrierHomeomorph_symm he hright, N.coordinate_map_eq]
    coordinate_map_smooth := N.pullbackOpen_coordinate_smooth hks
    coordinate_inverse := N.coordinate_inverse ∘ e
    coordinate_inverse_mem := fun x hx => N.coordinate_inverse_mem (e x) hx
    coordinate_inverse_left := by
      intro z
      change N.coordinate_inverse (e (eU.symm (N.coordinate z))) = _
      rw [N.pullbackOpenCarrierHomeomorph_symm he hright, hright (N.coordinate z).property]
      exact N.coordinate_inverse_left z
    coordinate_inverse_right := by
      intro x hx
      apply Subtype.ext
      change (eU.symm (N.coordinate _ ) : X) = x
      dsimp only [Function.comp_apply]
      rw [N.coordinate_inverse_right (e x) hx,
        N.pullbackOpenCarrierHomeomorph_symm he hright]
      exact hleft x
    coordinate_inverse_smooth := N.coordinate_inverse_smooth.comp hes.contMDiffOn (fun _ hx => hx)
    central_sphere := e ⁻¹' N.central_sphere
    central_sphere_eq := by
      ext x
      change e x ∈ N.central_sphere ↔ x ∈ (k ∘ N.coordinate_map) '' (univ ×ˢ {0})
      rw [N.central_sphere_eq]
      constructor
      · rintro ⟨z, hz, hzx⟩
        exact ⟨z, hz, by change k (N.coordinate_map z) = x; rw [hzx, hleft x]⟩
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z, hz, ?_⟩
        exact (hright (N.central_sphere_subset (N.central_sphere_eq ▸ mem_image_of_mem _ hz))).symm
    center_on_central_sphere := by
      change e (k N.center) ∈ N.central_sphere
      rw [hright hcenter]
      exact N.center_on_central_sphere
    central_sphere_subset := fun _ hx => N.central_sphere_subset hx
    metric_comparison := ⟨N.metric_comparison.close.congr (fun z hz v w =>
      congrArg (fun a : ℝ => N.scale⁻¹ ^ 2 * a) (N.pullbackOpen_metric hes hks hright hmetric z hz v w))⟩ }

theorem pullbackOpen_region (a b : ℝ) :
    (N.pullbackOpen D he hes hks hleft hright hmetric).region a b = e ⁻¹' N.region a b := rfl

end PoincareConjecture.EpsilonNeck
