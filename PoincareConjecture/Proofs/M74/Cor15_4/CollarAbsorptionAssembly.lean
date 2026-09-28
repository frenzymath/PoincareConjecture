import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionAssemblyMaps
import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionSphereGluing










set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M74.CollarEndChartData

variable {Y : GeneralizedSliceCarrier.{u}} (D : CollarEndChartData Y)



theorem assembledMap_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ D.assembledMap D.assembledSource := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rcases D.cover_cases x with hx₁ | hx₂ | ⟨q, rfl⟩
  · have hlocal := contDiff_collarBallMap.contMDiff.contMDiffAt.comp x
      (D.first_smooth.contMDiffAt (D.first.open_source.mem_nhds hx₁))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [D.first.open_source.mem_nhds hx₁] with y hy
    exact D.assembledMap_first hy
  · have hne : D.second x ≠ 0 := fun h => hx ((D.second_eq_zero_iff hx₂).mp h)
    have hlocal := (collarOuterMap_contDiffAt hne).contMDiffAt.comp x
      (D.second_smooth.contMDiffAt (D.second.open_source.mem_nhds hx₂))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [D.second.open_source.mem_nhds hx₂] with y hy
    exact D.assembledMap_second hy
  · have ht := D.neck.map_source (D.central_mem_source q)
    have hlocal := collarRadialMap_contMDiff.contMDiffAt.comp (D.neck (q, 0))
      (D.neck_inverse_smooth.contMDiffAt (D.neck.open_target.mem_nhds ht))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [D.neck.open_target.mem_nhds ht] with y hy
    have heq := D.assembledMap_neck (D.neck.map_target hy)
    rwa [D.neck.right_inv hy] at heq




theorem assembledInverse_contMDiff (q0 : UnitTwoSphere) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (D.assembledInverse q0) := by
  intro z
  rcases lt_trichotomy ‖z‖ 2 with hz | hz | hz
  · have hball : z ∈ ball (0 : StandardCapSpace) 2 := mem_ball_zero_iff.mpr hz
    have hlocal := D.first_inverse_smooth.contMDiffAt.comp z
      (contDiffOn_collarBallInverse.contDiffAt (isOpen_ball.mem_nhds hball)).contMDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hball] with w hw
    simp only [assembledInverse, if_pos (mem_ball_zero_iff.mp hw), Function.comp_apply]
  · have hne : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; norm_num)
    have hp : collarRadialInverse q0 z ∈ D.neck.source := by
      simpa only [collarRadialInverse, hz, collarHeight_two]
        using D.central_mem_source (sphereNormalize q0 z)
    have hi := (collarRadialInverse_contMDiffOn q0).contMDiffAt
      (isOpen_compl_singleton.mem_nhds hne)
    have hlocal := (D.neck_smooth.contMDiffAt
      (D.neck.open_source.mem_nhds hp)).comp z hi
    apply hlocal.congr_of_eventuallyEq
    have hsource := hi.continuousAt.eventually (D.neck.open_source.mem_nhds hp)
    filter_upwards [isOpen_compl_singleton.mem_nhds hne, hsource] with w hwn hw
    exact D.assembledInverse_eq_neck q0 hwn hw
  · have hopen : IsOpen {w : StandardCapSpace | 2 < ‖w‖} :=
      isOpen_lt continuous_const continuous_norm
    have hlocal := D.second_inverse_smooth.contMDiffAt.comp z
      (collarOuterInverse_contDiffAt hz).contMDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hz] with w hw
    simp only [assembledInverse, if_neg (not_lt_of_ge hw.le), if_pos hw, Function.comp_apply]




noncomputable def assembledChart (q0 : UnitTwoSphere) :
    OpenPartialHomeomorph Y.carrier StandardCapSpace where
  toFun := D.assembledMap
  invFun := D.assembledInverse q0
  source := D.assembledSource
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := (D.assembledInverse_spec q0 z).1
  left_inv' _ hx := D.assembledInverse_map q0 hx
  right_inv' z _ := (D.assembledInverse_spec q0 z).2
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := D.assembledMap_contMDiffOn.continuousOn
  continuousOn_invFun := (D.assembledInverse_contMDiff q0).continuous.continuousOn



@[simp] theorem assembledChart_source (q0 : UnitTwoSphere) :
    (D.assembledChart q0).source = {D.second.symm 0}ᶜ := rfl



@[simp] theorem assembledChart_target (q0 : UnitTwoSphere) :
    (D.assembledChart q0).target = univ := rfl



@[simp] theorem assembledChart_apply (q0 : UnitTwoSphere) (x : Y.carrier) :
    D.assembledChart q0 x = D.assembledMap x := rfl



@[simp] theorem assembledChart_symm_apply (q0 : UnitTwoSphere) (z : StandardCapSpace) :
    (D.assembledChart q0).symm z = D.assembledInverse q0 z := rfl




noncomputable def sphereDiffeomorph (q0 : UnitTwoSphere) (v : ThreeSphere) :
    Diffeomorph (𝓡 3) (𝓡 3) Y.carrier ThreeSphere ∞ := by
  apply diffeomorphOfSphereCharts Y v (D.assembledChart q0) (D.swap.assembledChart q0)
    rfl rfl
  · apply eq_univ_of_forall
    intro x
    change x ≠ D.second.symm 0 ∨ x ≠ D.first.symm 0
    by_cases hx : x = D.second.symm 0
    · exact Or.inr (fun heq => D.centers_ne (heq.symm.trans hx))
    · exact Or.inl hx
  · intro x hx
    change x ≠ D.first.symm 0 ↔ D.assembledMap x ≠ 0
    exact (not_congr (D.assembledMap_eq_zero_iff q0 hx)).symm
  · intro x _ _
    exact D.assembledMap_swap x
  · exact D.assembledMap_contMDiffOn
  · exact D.swap.assembledMap_contMDiffOn
  · exact D.assembledInverse_contMDiff q0
  · exact D.swap.assembledInverse_contMDiff q0

end PoincareConjecture.M74.CollarEndChartData
