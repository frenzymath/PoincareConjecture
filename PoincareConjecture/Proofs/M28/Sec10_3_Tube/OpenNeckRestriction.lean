import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions
import PoincareConjecture.Proofs.M28.Generalized.CylinderComparisonCongruence
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem intrinsicOpenMetric_scalarCurvature (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M)
    (DU : LeviCivitaData (intrinsicOpenMetric g V))
    (D : LeviCivitaData g) (x : V) :
    DU.scalarCurvature x = D.scalarCurvature (x : M) := by
  exact DU.scalarCurvature_eq_of_local_isometry D isOpen_univ
    (contMDiff_subtype_val (I := 𝓡 3) (U := V)).contMDiffOn
    (fun y _ v w => intrinsicOpenMetric_inner g V y v w) (mem_univ x)

end PoincareConjecture.M28

namespace PoincareConjecture.EpsilonNeck

open PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

def openRestrictionCenter (N : EpsilonNeck g) (V : TopologicalSpace.Opens M)
    (hNV : N.carrier ⊆ (V : Set M)) : V :=
  ⟨N.center, hNV (N.central_sphere_subset N.center_on_central_sphere)⟩

def openRestrictionCarrierHomeomorph (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M)) :
    N.carrier ≃ₜ ((Subtype.val : V → M) ⁻¹' N.carrier) where
  toFun x := ⟨⟨x.val, hNV x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  continuous_toFun :=
    ((continuous_subtype_val : Continuous (fun x : N.carrier => x.val)).subtype_mk
      (fun x => hNV x.property)).subtype_mk (fun x => x.property)
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x => x.property)

def openRestrictionCoordinate (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M)) :
    NeckDomain N.epsilon ≃ₜ ((Subtype.val : V → M) ⁻¹' N.carrier) :=
  N.coordinate.trans (N.openRestrictionCarrierHomeomorph V hNV)

def openRestrictionMap (N : EpsilonNeck g) (V : TopologicalSpace.Opens M)
    (hNV : N.carrier ⊆ (V : Set M)) : RoundCylinderSpace → V :=
  (V.openPartialHomeomorphSubtypeCoe ⟨N.openRestrictionCenter V hNV⟩).symm ∘
    N.coordinate_map

theorem openRestrictionMap_val_on_strip (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    (N.openRestrictionMap V hNV z : M) = N.coordinate_map z := by
  let e := V.openPartialHomeomorphSubtypeCoe ⟨N.openRestrictionCenter V hNV⟩
  change e (e.symm (N.coordinate_map z)) = N.coordinate_map z
  exact e.right_inv (by
    simpa only [e, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
      using hNV (N.coordinate_map_mem_of_axial z hz))

theorem openRestrictionCoordinate_eq_map (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (z : NeckDomain N.epsilon) :
    (N.openRestrictionCoordinate V hNV z).val =
      N.openRestrictionMap V hNV (z.1, (z.2 : ℝ)) := by
  apply Subtype.ext
  change (N.coordinate z).val = (N.openRestrictionMap V hNV _ : M)
  rw [N.openRestrictionMap_val_on_strip V hNV _ z.2.property]
  exact N.coordinate_map_eq z

theorem openRestrictionMap_smooth (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M)) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (N.openRestrictionMap V hNV)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  exact (openSubtypeInverse_contMDiffOn V
    ⟨N.openRestrictionCenter V hNV⟩).comp N.coordinate_map_smooth
      (fun z hz => hNV (N.coordinate_map_mem_of_axial z hz.2))

theorem openRestrictionInverse_smooth (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (N.coordinate_inverse ∘ (Subtype.val : V → M))
      (Subtype.val ⁻¹' N.carrier) := by
  exact N.coordinate_inverse_smooth.comp
    (contMDiff_subtype_val (I := 𝓡 3) (U := V)).contMDiffOn
    (fun _ hx => hx)

theorem openRestriction_central_sphere_eq (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M)) :
    (Subtype.val : V → M) ⁻¹' N.central_sphere =
      N.openRestrictionMap V hNV '' (univ ×ˢ ({0} : Set ℝ)) := by
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    exact ⟨neg_neg_of_pos he, he⟩
  ext x
  constructor
  · intro hx
    change x.val ∈ N.central_sphere at hx
    rw [N.central_sphere_eq] at hx
    rcases hx with ⟨z, hz, hzx⟩
    have hz0 : z.2 = 0 := by simpa using hz.2
    refine ⟨z, hz, Subtype.ext ?_⟩
    rw [N.openRestrictionMap_val_on_strip V hNV z (by simpa [hz0] using hzero)]
    exact hzx
  · rintro ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := by simpa using hz.2
    change (N.openRestrictionMap V hNV z).val ∈ N.central_sphere
    rw [N.openRestrictionMap_val_on_strip V hNV z (by simpa [hz0] using hzero),
      N.central_sphere_eq]
    exact ⟨z, hz, rfl⟩

theorem openRestriction_tensor_eq_on_strip (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback (intrinsicOpenMetric g V)
        (N.openRestrictionMap V hNV) z v w =
      roundCylinderPullback g N.coordinate_map z v w := by
  have hz' : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨mem_univ _, hz⟩
  have hstrip : univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∈ 𝓝 z :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds hz'
  have heq : (Subtype.val ∘ N.openRestrictionMap V hNV) =ᶠ[𝓝 z]
      N.coordinate_map := by
    filter_upwards [hstrip] with y hy
    exact N.openRestrictionMap_val_on_strip V hNV y hy.2
  have hderiv_v :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          (Subtype.val ∘ N.openRestrictionMap V hNV) z v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v := by
    exact congrArg
      (fun L : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z →L[ℝ]
        TangentSpace (𝓡 3) ((Subtype.val ∘ N.openRestrictionMap V hNV) z) => L v)
      (heq.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  have hderiv_w :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          (Subtype.val ∘ N.openRestrictionMap V hNV) z w =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w := by
    exact congrArg
      (fun L : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z →L[ℝ]
        TangentSpace (𝓡 3) ((Subtype.val ∘ N.openRestrictionMap V hNV) z) => L w)
      (heq.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  have hf : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (N.openRestrictionMap V hNV) z :=
    (N.openRestrictionMap_smooth V hNV z hz').contMDiffAt hstrip
  have hcomp_v := mfderiv_comp_apply z
    ((contMDiff_subtype_val (U := V)
      (N.openRestrictionMap V hNV z)).mdifferentiableAt (n := ∞) (by simp))
    (hf.mdifferentiableAt (n := ∞) (by simp)) v
  have hcomp_w := mfderiv_comp_apply z
    ((contMDiff_subtype_val (U := V)
      (N.openRestrictionMap V hNV z)).mdifferentiableAt (n := ∞) (by simp))
    (hf.mdifferentiableAt (n := ∞) (by simp)) w
  change (intrinsicOpenMetric g V).inner (N.openRestrictionMap V hNV z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (N.openRestrictionMap V hNV) z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (N.openRestrictionMap V hNV) z w) = _
  rw [intrinsicOpenMetric_inner, ← hcomp_v, ← hcomp_w,
    hderiv_v, hderiv_w, N.openRestrictionMap_val_on_strip V hNV z hz]
  rfl

def restrictOpen (N : EpsilonNeck g) (V : TopologicalSpace.Opens M)
    (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    EpsilonNeck (intrinsicOpenMetric g V) where
  epsilon := N.epsilon
  epsilon_pos := N.epsilon_pos
  epsilon_lt_half := N.epsilon_lt_half
  scale := N.scale
  scale_pos := N.scale_pos
  center := N.openRestrictionCenter V hNV
  connection := DU
  scalar_center_pos := by
    rw [intrinsicOpenMetric_scalarCurvature g V DU N.connection]
    exact N.scalar_center_pos
  scale_eq_scalar := by
    rw [intrinsicOpenMetric_scalarCurvature g V DU N.connection]
    exact N.scale_eq_scalar
  carrier := Subtype.val ⁻¹' N.carrier
  carrier_open := N.carrier_open.preimage continuous_subtype_val
  coordinate := N.openRestrictionCoordinate V hNV
  coordinate_map := N.openRestrictionMap V hNV
  coordinate_map_eq := N.openRestrictionCoordinate_eq_map V hNV
  coordinate_map_smooth := N.openRestrictionMap_smooth V hNV
  coordinate_inverse := N.coordinate_inverse ∘ Subtype.val
  coordinate_inverse_mem := fun x hx => N.coordinate_inverse_mem x.val hx
  coordinate_inverse_left := by
    intro z
    change N.coordinate_inverse (N.coordinate z).val = _
    exact N.coordinate_inverse_left z
  coordinate_inverse_right := by
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    change (N.coordinate _).val = x.val
    exact congrArg Subtype.val (N.coordinate_inverse_right x.val hx)
  coordinate_inverse_smooth := N.openRestrictionInverse_smooth V
  central_sphere := Subtype.val ⁻¹' N.central_sphere
  central_sphere_eq := N.openRestriction_central_sphere_eq V hNV
  center_on_central_sphere := N.center_on_central_sphere
  central_sphere_subset := fun _ hx => N.central_sphere_subset hx
  metric_comparison := ⟨by
    apply cylinderClose_of_eqOn_strip N.metric_comparison.close
    intro z hz v w
    rw [N.openRestriction_tensor_eq_on_strip V hNV z hz v w]⟩

@[simp] theorem restrictOpen_epsilon (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DU).epsilon = N.epsilon := rfl

@[simp] theorem restrictOpen_scale (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DU).scale = N.scale := rfl

@[simp] theorem restrictOpen_connection (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DU).connection = DU := rfl

@[simp] theorem restrictOpen_center_val (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    ((N.restrictOpen V hNV DU).center : M) = N.center := rfl

@[simp] theorem restrictOpen_carrier (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DU).carrier = Subtype.val ⁻¹' N.carrier := rfl

@[simp] theorem restrictOpen_central_sphere (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DU).central_sphere = Subtype.val ⁻¹' N.central_sphere := rfl

@[simp] theorem restrictOpen_region (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) (a b : ℝ) :
    (N.restrictOpen V hNV DU).region a b = Subtype.val ⁻¹' N.region a b := rfl

@[simp] theorem restrictOpen_coordinate_inverse (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V)) :
    (N.restrictOpen V hNV DU).coordinate_inverse =
      N.coordinate_inverse ∘ Subtype.val := rfl

theorem restrictOpen_coordinate_map_val_on_strip (N : EpsilonNeck g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (DU : LeviCivitaData (intrinsicOpenMetric g V))
    (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ((N.restrictOpen V hNV DU).coordinate_map z : M) = N.coordinate_map z :=
  N.openRestrictionMap_val_on_strip V hNV z hz

end PoincareConjecture.EpsilonNeck
