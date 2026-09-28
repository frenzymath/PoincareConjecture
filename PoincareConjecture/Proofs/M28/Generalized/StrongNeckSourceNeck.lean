import PoincareConjecture.Proofs.M28.Generalized.StrongNeckNormalizedFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSlice
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckNormalizedMetric
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

noncomputable section

abbrev strongNeckSourceOpen
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    TopologicalSpace.Opens (F.slice t).carrier :=
  strongNeckOpen S

def strongNeckSourceCenter
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    (strongNeckSourceOpen S).carrier :=
  ⟨S.center, S.central_sphere_subset S.center_on_central_sphere⟩

def strongNeckSourceUnivHomeomorph
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    (strongNeckSourceOpen S).carrier ≃ₜ
      (Set.univ : Set (strongNeckSourceOpen S).carrier) where
  toFun x := ⟨x, mem_univ x⟩
  invFun x := x.1
  left_inv x := rfl
  right_inv x := Subtype.ext (by rfl)
  continuous_toFun := continuous_id.subtype_mk (fun _ => mem_univ _)
  continuous_invFun := continuous_subtype_val

def strongNeckSourceCoordinate
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    NeckDomain epsilon ≃ₜ
      (Set.univ : Set (strongNeckSourceOpen S).carrier) :=
  S.coordinate.trans (strongNeckSourceUnivHomeomorph S)

def strongNeckSourceMap
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    RoundCylinderSpace → (strongNeckSourceOpen S).carrier := by
  classical
  let c := strongNeckSourceCenter S
  exact fun z ↦ if hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ then
    ⟨S.coordinate_map z, by
      have hz' := S.coordinate_map_eq (z.1, ⟨z.2, hz⟩)
      rw [← hz']
      exact (S.coordinate (z.1, ⟨z.2, hz⟩)).property⟩
    else c

theorem strongNeckSourceMap_val_on_strip
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    (strongNeckSourceMap S z).val = S.coordinate_map z := by
  unfold strongNeckSourceMap
  dsimp
  rw [dif_pos hz]

theorem strongNeckSourceMap_eq_coordinate
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) (z : NeckDomain epsilon) :
    (strongNeckSourceMap S (z.1, (z.2 : ℝ))).val =
      S.coordinate z := by
  rw [strongNeckSourceMap_val_on_strip S (z.1, (z.2 : ℝ)) z.2.property]
  simpa using (S.coordinate_map_eq z).symm

def strongNeckSourceInverse
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    (strongNeckSourceOpen S).carrier → RoundCylinderSpace :=
  fun x ↦ S.coordinate_inverse x.val

theorem strongNeckSourceInverse_mem
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (x : (strongNeckSourceOpen S).carrier) :
    strongNeckSourceInverse S x ∈
      Set.univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
  exact ⟨mem_univ _, S.coordinate_inverse_mem x.val x.property⟩

theorem strongNeckSourceMap_smooth
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckSourceOpen S).carrier :=
      TopologicalSpace.Opens.instChartedSpace (strongNeckSourceOpen S)
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (strongNeckSourceMap S)
      (Set.univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
  intro z hz
  apply (ContMDiffWithinAt.subtypeVal_comp_iff
    (strongNeckSourceOpen S) (strongNeckSourceMap S)
    (Set.univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) z).mp
  have h := S.coordinate_map_smooth z hz
  apply h.congr
  · intro y hy
    change (strongNeckSourceMap S y).val = S.coordinate_map y
    exact strongNeckSourceMap_val_on_strip S y hy.2
  · change (strongNeckSourceMap S z).val = S.coordinate_map z
    exact strongNeckSourceMap_val_on_strip S z hz.2

theorem strongNeckSourceInverse_left
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) (z : NeckDomain epsilon) :
    strongNeckSourceInverse S
        ((strongNeckSourceCoordinate S z).val) =
      (z.1, (z.2 : ℝ)) := by
  dsimp [strongNeckSourceInverse, strongNeckSourceCoordinate,
    strongNeckSourceUnivHomeomorph]
  exact S.coordinate_inverse_left z

theorem strongNeckSourceInverse_right
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (x : (strongNeckSourceOpen S).carrier) :
    (strongNeckSourceMap S (strongNeckSourceInverse S x)).val = x.val := by
  have hxmem : x.val ∈ S.carrier := x.property
  have hi := S.coordinate_inverse_mem x.val hxmem
  change (strongNeckSourceMap S (S.coordinate_inverse x.val)).val = x.val
  rw [strongNeckSourceMap_val_on_strip S _ hi]
  exact S.coordinate_inverse_right x.val hxmem

theorem strongNeckSourceInverse_smooth
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckSourceOpen S).carrier :=
      TopologicalSpace.Opens.instChartedSpace (strongNeckSourceOpen S)
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (strongNeckSourceInverse S) (Set.univ : Set (strongNeckSourceOpen S).carrier) := by
  intro x hx
  exact S.coordinate_inverse_smooth.comp contMDiff_subtype_val.contMDiffOn
    (fun y hy ↦ y.property) x hx

theorem strongNeckSourceCenter_mem_image
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon) :
    strongNeckSourceCenter S ∈
    strongNeckSourceMap S '' (Set.univ ×ˢ ({0} : Set ℝ)) := by
  have hcenter : S.center ∈ S.central_sphere := S.center_on_central_sphere
  rw [S.central_sphere_eq] at hcenter
  rcases hcenter with ⟨z, hz, hzc⟩
  have hz0 : z.2 = 0 := by simpa using hz.2
  have hz' : (z.1, (0 : ℝ)) ∈ Set.univ ×ˢ ({0} : Set ℝ) :=
    ⟨mem_univ _, by simp⟩
  refine ⟨(z.1, (0 : ℝ)), hz', ?_⟩
  apply Subtype.ext
  rw [strongNeckSourceMap_val_on_strip S _]
  · rw [← hz0, hzc]
    rfl
  · exact ⟨by
      have he : 0 < epsilon⁻¹ := inv_pos.mpr S.epsilon_pos
      linarith, by
      have he : 0 < epsilon⁻¹ := inv_pos.mpr S.epsilon_pos
      linarith⟩

theorem strongNeckSource_tensor_eq_on_strip
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (H : RescaledRawCylinderData (C := F.slice t)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
    (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckOpen S).carrier :=
      TopologicalSpace.Opens.instChartedSpace (strongNeckOpen S)
    roundCylinderPullback (H.rescaling.flow.metric 0)
        (strongNeckSourceMap S) z v w =
      S.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric t)
        S.coordinate_map z v w := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckOpen S).carrier :=
    TopologicalSpace.Opens.instChartedSpace (strongNeckOpen S)
  have hz' : z ∈ Set.univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨mem_univ _, hz⟩
  have hstrip : Set.univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ ∈ 𝓝 z :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds hz'
  have heq : (Subtype.val ∘ strongNeckSourceMap S) =ᶠ[𝓝 z]
      S.coordinate_map := by
    filter_upwards [hstrip] with y hy
    exact strongNeckSourceMap_val_on_strip S y hy.2
  have hderiv_v :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          (Subtype.val ∘ strongNeckSourceMap S) z v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          S.coordinate_map z v := by
    exact congrArg
      (fun L : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z →L[ℝ]
        TangentSpace (𝓡 3) ((Subtype.val ∘ strongNeckSourceMap S) z) => L v)
      (heq.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  have hderiv_w :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          (Subtype.val ∘ strongNeckSourceMap S) z w =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          S.coordinate_map z w := by
    exact congrArg
      (fun L : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z →L[ℝ]
        TangentSpace (𝓡 3) ((Subtype.val ∘ strongNeckSourceMap S) z) => L w)
      (heq.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (I' := 𝓡 3))
  have hf : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (strongNeckSourceMap S) z := by
    exact (strongNeckSourceMap_smooth S z hz').contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz')
  have hcomp_v := mfderiv_comp_apply z
    ((contMDiff_subtype_val (U := strongNeckOpen S)
      (strongNeckSourceMap S z)).mdifferentiableAt (n := ∞) (by simp))
    (hf.mdifferentiableAt (n := ∞) (by simp)) v
  have hcomp_w := mfderiv_comp_apply z
    ((contMDiff_subtype_val (U := strongNeckOpen S)
      (strongNeckSourceMap S z)).mdifferentiableAt (n := ∞) (by simp))
    (hf.mdifferentiableAt (n := ∞) (by simp)) w
  have hm := GeneralizedStrongNeck.rescaled_metric_at_zero S H
    (strongNeckSourceMap S z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (strongNeckSourceMap S) z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (strongNeckSourceMap S) z w)
  change (H.rescaling.flow.metric 0).inner (strongNeckSourceMap S z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (strongNeckSourceMap S) z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (strongNeckSourceMap S) z w) = _
  calc
    _ = S.scale⁻¹ ^ 2 * (F.metric t).inner (strongNeckSourceMap S z).val
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          (strongNeckSourceMap S z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            (strongNeckSourceMap S) z v))
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          (strongNeckSourceMap S z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            (strongNeckSourceMap S) z w)) := hm
    _ = S.scale⁻¹ ^ 2 * (F.metric t).inner (strongNeckSourceMap S z).val
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          (Subtype.val ∘ strongNeckSourceMap S) z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          (Subtype.val ∘ strongNeckSourceMap S) z w) := by
      rw [← hcomp_v, ← hcomp_w]
      rfl
    _ = S.scale⁻¹ ^ 2 * (F.metric t).inner (S.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          S.coordinate_map z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          S.coordinate_map z w) := by
      rw [hderiv_v, hderiv_w,
        strongNeckSourceMap_val_on_strip S z hz]
    _ = S.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric t)
        S.coordinate_map z v w := by rfl

noncomputable def GeneralizedStrongNeck.rescaled_source_neck
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (hepsilon : epsilon < 1 / 2)
    (H : RescaledRawCylinderData (C := F.slice t)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckOpen S).carrier :=
      TopologicalSpace.Opens.instChartedSpace (strongNeckOpen S)
    EpsilonNeck (H.rescaling.flow.metric 0) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (strongNeckOpen S).carrier :=
    TopologicalSpace.Opens.instChartedSpace (strongNeckOpen S)
  have hscalar :
      (H.rescaling.flow.connection 0).scalarCurvature
          (strongNeckSourceCenter S) = 1 := by
    simpa [strongNeckSourceCenter] using
      (GeneralizedStrongNeck.rescaled_scalar_at_center S H)
  have hcoord_eq : ∀ z : NeckDomain epsilon,
      strongNeckSourceCoordinate S z =
        strongNeckSourceMap S (z.1, (z.2 : ℝ)) := by
    intro z
    apply Subtype.ext
    simpa [strongNeckSourceCoordinate, strongNeckSourceUnivHomeomorph] using
      (strongNeckSourceMap_eq_coordinate S z).symm
  have hclose : RoundCylinderClose epsilon 0
      (fun z v w ↦ (1 : ℝ)⁻¹ ^ 2 *
        roundCylinderPullback (H.rescaling.flow.metric 0)
          (strongNeckSourceMap S) z v w) := by
    have htop := (strongNeck_top_comparison S).close
    have hEq : ∀ z : RoundCylinderSpace,
        z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ v w,
        (S.scale⁻¹ ^ 2 * roundCylinderPullback (F.metric t)
          S.coordinate_map z v w) =
          (1 : ℝ)⁻¹ ^ 2 * roundCylinderPullback
            (H.rescaling.flow.metric 0) (strongNeckSourceMap S) z v w := by
      intro z hz v w
      rw [strongNeckSource_tensor_eq_on_strip S H z hz v w]
      norm_num
    simpa using (cylinderClose_of_eqOn_strip htop hEq)
  refine {
    epsilon := epsilon
    epsilon_pos := S.epsilon_pos
    epsilon_lt_half := hepsilon
    scale := 1
    scale_pos := by norm_num
    center := strongNeckSourceCenter S
    connection := H.rescaling.flow.connection 0
    scalar_center_pos := by rw [hscalar]; norm_num
    scale_eq_scalar := by rw [hscalar]; norm_num
    carrier := Set.univ
    carrier_open := isOpen_univ
    coordinate := strongNeckSourceCoordinate S
    coordinate_map := strongNeckSourceMap S
    coordinate_map_eq := hcoord_eq
    coordinate_map_smooth := strongNeckSourceMap_smooth S
    coordinate_inverse := strongNeckSourceInverse S
    coordinate_inverse_mem := by
      intro x hx
      exact strongNeckSourceInverse_mem S x
    coordinate_inverse_left := strongNeckSourceInverse_left S
    coordinate_inverse_right := by
      intro x hx
      have hi := strongNeckSourceInverse_mem S x
      apply Subtype.ext
      rw [hcoord_eq]
      exact Subtype.ext (strongNeckSourceInverse_right S x)
    coordinate_inverse_smooth := strongNeckSourceInverse_smooth S
    central_sphere := strongNeckSourceMap S ''
      (Set.univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere := strongNeckSourceCenter_mem_image S
    central_sphere_subset := by
      intro x hx
      exact mem_univ x
    metric_comparison := ⟨by
      simpa using hclose⟩ }

end

end PoincareConjecture.M28
