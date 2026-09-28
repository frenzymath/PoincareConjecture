import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckOrdinaryPullback
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckRestriction
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem ordinaryChapter11_exists_sourceStrongNeck
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
    {K : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (G) C origin scale K U)
    (hU : IsOpen U) (hK : IsPreconnected K) (hzero : 0 ∈ K)
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    (hNU : N.carrier ⊆ U) (hI : Ioc (-1 : ℝ) 0 ⊆ K)
    (sigma : ℝ) (hsigma : 0 < sigma) (hscale : scale = sigma⁻¹ ^ 2)
    (hscalar : 0 < (G).scalar (e.pointMap 0 hzero N.center))
    (hsigmaScalar : sigma = ((G).scalar (e.pointMap 0 hzero N.center)) ^ (-1 / 2 : ℝ))
    (hclose : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback e N.coordinate_map)) :
    ∃ Ns : GeneralizedStrongNeck (G) (origin + 0 / scale) N.epsilon,
      Ns.center = e.forward 0 hzero N.center := by
  subst scale
  have hzero' : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  let f := e.forward 0 hzero
  let fInv := e.inverse 0 hzero
  let V := f '' N.carrier
  let c := N.coordinate.trans (e.restrictedSpatialHomeomorph hNU 0 hzero)
  let coordinate := f ∘ N.coordinate_map
  let inverse := N.coordinate_inverse ∘ fInv
  let e' := ordinaryChapter11PushedCylinder R e N.center hzero N.carrier
    (Ioc (-1 : ℝ) 0) hI
  have hinv (x : ((G).slice (origin + 0 / sigma⁻¹ ^ 2)).carrier) (hx : x ∈ V) :
      fInv x ∈ N.carrier := by
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [fInv, f, e.left_inverse 0 hzero (hNU hy)] using hy
  have hcoordinate : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    (e.forward_smooth 0 hzero).comp N.coordinate_map_smooth
      (fun _ hz => hNU (N.coordinate_map_mem_of_axial_mem hz.2))
  have hinverse : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse V :=
    N.coordinate_inverse_smooth.comp
      ((e.inverse_smooth 0 hzero).mono (image_mono hNU)) hinv
  have hcomparison : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback e' coordinate) := by
    apply hclose.congr_cylinder
    intro s hs z hz v w
    exact (ordinaryChapter11PushedCylinder_cylinderPullback_eq R e hU hK N.center
      hzero N.carrier_open hNU (Ioc (-1 : ℝ) 0) hI (convex_Ioc _ _).isPreconnected
      hzero' hs
      ((N.coordinate_map_smooth.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt
          (by simp)) (N.coordinate_map_mem_of_axial_mem hz) v w).symm
  refine ⟨{
    epsilon_pos := N.epsilon_pos
    center := f N.center
    scalar_center_pos := hscalar
    scale := sigma
    scale_pos := hsigma
    scale_scalar := hsigmaScalar
    carrier := V
    carrier_open := e.isOpen_forward_image hU N.carrier_open hNU hzero
    coordinate := c
    coordinate_map := coordinate
    coordinate_map_eq := ?_
    coordinate_map_smooth := hcoordinate
    coordinate_inverse := inverse
    coordinate_inverse_mem := fun x hx => (N.coordinate_inverse_mem _ (hinv x hx)).2
    coordinate_inverse_left := ?_
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := hinverse
    central_sphere := f '' N.central_sphere
    central_sphere_eq := ?_
    center_on_central_sphere := mem_image_of_mem f N.center_on_central_sphere
    central_sphere_subset := image_mono N.central_sphere_subset
    time_cylinder := e'
    cylinder_identity := ?_
    metric_comparison := hcomparison
  }, rfl⟩
  · intro z
    exact congrArg f (N.coordinate_map_eq z)
  · intro z
    change N.coordinate_inverse (e.inverse 0 hzero (e.forward 0 hzero (N.coordinate z))) = _
    rw [e.left_inverse 0 hzero (hNU (N.coordinate z).property)]
    exact N.coordinate_inverse_left z
  · intro x hx
    have hy := hinv x hx
    have hN := congrArg (fun y : N.carrier => (y : C.carrier))
      (N.coordinate_inverse_right (fInv x) hy)
    rw [N.coordinate_map_eq] at hN
    change f (N.coordinate_map (N.coordinate_inverse (fInv x))) = x
    exact (congrArg f hN).trans (e.right_inverse 0 hzero ((image_mono hNU) hx))
  · rw [N.central_sphere_eq, image_image]
    rfl
  · intro h x _
    exact ordinaryChapter11PushedCylinder_zero_identity R e N.center hzero N.carrier
      (Ioc (-1 : ℝ) 0) hI h x

end PoincareConjecture.M34
