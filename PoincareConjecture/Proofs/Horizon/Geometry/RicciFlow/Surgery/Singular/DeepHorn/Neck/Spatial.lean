import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareConjecture

namespace DeepHorn

theorem roundCylinderIteratedDerivative_congr_axial
    {J : Set ℝ} (hJ : IsOpen J) {B B' : RoundCylinderTwoTensor}
    (hB : ∀ z : RoundCylinderSpace, z.2 ∈ J → ∀ v w, B z v w = B' z v w)
    (s : ℝ) (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (k : ℕ) (p : RoundCylinderCoordinates) (hp : p.2 ∈ J) :
    roundCylinderIteratedDerivative s c B k p =
      roundCylinderIteratedDerivative s c B' k p := by
  induction k generalizing p with
  | zero =>
      funext a
      simp only [roundCylinderIteratedDerivative, roundCylinderTensorCoefficient,
        hB (c.symm p.1, p.2) hp]
  | succ k ih =>
      funext a
      have heq : (fun q : RoundCylinderCoordinates =>
          roundCylinderIteratedDerivative s c B k q (fun i => a i.succ)) =ᶠ[𝓝 p]
          (fun q => roundCylinderIteratedDerivative s c B' k q (fun i => a i.succ)) :=
        Filter.eventuallyEq_of_mem ((hJ.preimage continuous_snd).mem_nhds hp)
          (fun q hq => congrFun (ih q hq) _)
      simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative, ih p hp]
      apply congrArg (fun r : ℝ => r - _)
      exact congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
        L (roundCylinderCoordinateBasis (a 0))) (heq.fderiv_eq (𝕜 := ℝ))

theorem roundCylinderJetErrorSquared_congr_axial
    {J : Set ℝ} (hJ : IsOpen J) {B B' : RoundCylinderTwoTensor}
    (hB : ∀ z : RoundCylinderSpace, z.2 ∈ J → ∀ v w, B z v w = B' z v w)
    (s : ℝ) (k : ℕ) (z : RoundCylinderSpace) (hz : z.2 ∈ J) :
    roundCylinderJetErrorSquared s B k z = roundCylinderJetErrorSquared s B' k z := by
  unfold roundCylinderJetErrorSquared
  apply Finset.sum_congr rfl
  intro i hi
  rw [roundCylinderIteratedDerivative_congr_axial hJ hB s _ i _ hz]

theorem roundCylinderClose_congr_axial
    {epsilon s : ℝ} {B B' : RoundCylinderTwoTensor}
    (hB : ∀ z : RoundCylinderSpace, z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B z v w = B' z v w)
    (hclose : RoundCylinderClose epsilon s B) : RoundCylinderClose epsilon s B' := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hclose
  refine ⟨?_, bound, hbound, ?_⟩
  · intro q a b
    apply (hsmooth q a b).congr
    intro p hp
    exact (hB _ hp.2 _ _).symm
  · intro z hz
    rw [← roundCylinderJetErrorSquared_congr_axial isOpen_Ioo hB s _ z hz]
    exact hjet z hz

end DeepHorn

private theorem slicePullback_eq_of_identity
    {F : GeneralizedRicciFlowData.{u}} {t s : ℝ}
    {U : Set (F.slice t).carrier} (hU : IsOpen U)
    (f : (F.slice t).carrier → (F.slice s).carrier)
    (ht : s = t)
    (hf : ∀ x ∈ U, (⟨s, f x⟩ : F.point) = ⟨t, x⟩)
    {x : (F.slice t).carrier} (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    (F.metric s).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) =
      (F.metric t).inner x v w := by
  subst s
  have heq : f =ᶠ[𝓝 x] id := Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
    (fun y hy => by simpa using (Sigma.mk.inj (hf y hy)).2)
  rw [heq.mfderiv_eq, mfderiv_id]
  exact congrArg (fun y => (F.metric t).inner y v w) heq.eq_of_nhds

namespace GeneralizedStrongNeck

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}

theorem pullbackInner_zero (N : GeneralizedStrongNeck F t epsilon)
    (hzero : (0 : ℝ) ∈ Set.Ioc (-1 : ℝ) 0)
    {x : (F.slice t).carrier} (hx : x ∈ N.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    N.time_cylinder.pullbackInner 0 hzero x v w =
      N.scale⁻¹ ^ 2 * (F.metric t).inner x v w := by
  unfold GeneralizedFlowCylinder.pullbackInner
  congr 1
  exact slicePullback_eq_of_identity N.carrier_open
    (N.time_cylinder.forward 0 hzero) (by simp)
    (N.cylinder_identity hzero) hx v w

theorem pullback_zero (N : GeneralizedStrongNeck F t epsilon)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    generalizedCylinderPullback N.time_cylinder N.coordinate_map 0 z v w =
      N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric t) N.coordinate_map z v w := by
  have hzero : (0 : ℝ) ∈ Set.Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hx : N.coordinate_map z ∈ N.carrier := by
    have h := (N.coordinate (z.1, ⟨z.2, hz⟩)).property
    rwa [N.coordinate_map_eq] at h
  simp only [generalizedCylinderPullback, dif_pos hzero]
  exact N.pullbackInner_zero hzero hx _ _

theorem spatial_metric_comparison (N : GeneralizedStrongNeck F t epsilon) :
    RoundCylinderClose epsilon 0 (fun z v w =>
      N.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric t) N.coordinate_map z v w) := by
  apply DeepHorn.roundCylinderClose_congr_axial (fun z hz v w => N.pullback_zero hz v w)
  have hzero : (0 : ℝ) ∈ Set.Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := N.metric_comparison
  exact ⟨hsmooth 0 hzero, bound, hbound, hjet 0 hzero⟩


noncomputable def spatialNeck (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) : EpsilonNeck (F.metric t) where
  epsilon := epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := hepsilon
  scale := N.scale
  scale_pos := N.scale_pos
  center := N.center
  connection := F.connection t
  scalar_center_pos := N.scalar_center_pos
  scale_eq_scalar := N.scale_scalar
  carrier := N.carrier
  carrier_open := N.carrier_open
  coordinate := N.coordinate
  coordinate_map := N.coordinate_map
  coordinate_map_eq := N.coordinate_map_eq
  coordinate_map_smooth := N.coordinate_map_smooth
  coordinate_inverse := N.coordinate_inverse
  coordinate_inverse_mem := fun x hx => ⟨Set.mem_univ _, N.coordinate_inverse_mem x hx⟩
  coordinate_inverse_left := N.coordinate_inverse_left
  coordinate_inverse_right := by
    intro x hx
    apply Subtype.ext
    exact (N.coordinate_map_eq _).trans (N.coordinate_inverse_right x hx)
  coordinate_inverse_smooth := N.coordinate_inverse_smooth
  central_sphere := N.central_sphere
  central_sphere_eq := N.central_sphere_eq
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := N.central_sphere_subset
  metric_comparison := ⟨N.spatial_metric_comparison⟩

@[simp] theorem spatialNeck_epsilon (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) : (N.spatialNeck hepsilon).epsilon = epsilon := rfl

@[simp] theorem spatialNeck_center (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) : (N.spatialNeck hepsilon).center = N.center := rfl

@[simp] theorem spatialNeck_scale (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) : (N.spatialNeck hepsilon).scale = N.scale := rfl

@[simp] theorem spatialNeck_connection (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) :
    (N.spatialNeck hepsilon).connection = F.connection t := rfl

@[simp] theorem spatialNeck_carrier (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) : (N.spatialNeck hepsilon).carrier = N.carrier := rfl

@[simp] theorem spatialNeck_coordinate_map (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) :
    (N.spatialNeck hepsilon).coordinate_map = N.coordinate_map := rfl

@[simp] theorem spatialNeck_central_sphere (N : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2) :
    (N.spatialNeck hepsilon).central_sphere = N.central_sphere := rfl

end GeneralizedStrongNeck

end PoincareConjecture
