import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionAssembly
import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionRegionChart
import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionActualCollar
import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionRadial

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SmoothConnectedSumData

open M74 M25.Topology3D

variable {A B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)
  (EA : Diffeomorph (𝓡 3) (𝓡 3)
    (⟨S.first_ball.closedBallᶜ, S.first_ball.closedBall_closed.isOpen_compl⟩ :
      TopologicalSpace.Opens A.carrier) StandardCapSpace ∞)
  (epsilonA : ℝ) (hApos : 0 < epsilonA) (hAlt : epsilonA < 1)
  (hEA : ∀ (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo 0 epsilonA),
    EA ⟨S.first_ball.map ((1 + s) • q.val), S.first_ball.radial_mem_complement q
      ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩ = (1 / s) • q.val)
  (EB : Diffeomorph (𝓡 3) (𝓡 3)
    (⟨S.second_ball.closedBallᶜ, S.second_ball.closedBall_closed.isOpen_compl⟩ :
      TopologicalSpace.Opens B.carrier) StandardCapSpace ∞)
  (epsilonB : ℝ) (hBpos : 0 < epsilonB) (hBlt : epsilonB < 1)
  (hEB : ∀ (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo 0 epsilonB),
    EB ⟨S.second_ball.map ((1 + s) • q.val), S.second_ball.radial_mem_complement q
      ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩ = (1 / s) • q.val)

noncomputable def canonicalEndChartData (q0 : UnitTwoSphere)
    (D : DiffSphereIsotopyData S.sphere_gluing.symm) : CollarEndChartData C := by
  let w := min epsilonA (min epsilonB (1 / 2 : ℝ))
  have hwA : w ≤ epsilonA := min_le_left _ _
  have hwB : w ≤ epsilonB := (min_le_right _ _).trans (min_le_left _ _)
  have hw2 : w ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hw1 : w ≤ 1 := hw2.trans (by norm_num)
  have hwpos : 0 < w := lt_min hApos (lt_min hBpos (by norm_num))
  let R := radialDiffeomorph D q0 (a := 1) (b := 2) (by norm_num) (by norm_num)
  let EB' := EB.trans R
  let a0 := S.first_identify.euclideanEndChart
    S.first_ball.closedBall_closed.isOpen_compl EA S.first_open
  let a1 := S.second_identify.euclideanEndChart
    S.second_ball.closedBall_closed.isOpen_compl EB' S.second_open
  refine {
    first := a0
    second := a1
    first_target := rfl
    second_target := rfl
    disjoint := S.regions_disjoint
    first_smooth := S.first_identify.euclideanEndMap_contMDiffOn _ EA
    second_smooth := S.second_identify.euclideanEndMap_contMDiffOn _ EB'
    first_inverse_smooth := S.first_identify.euclideanEndInverse_contMDiff _ EA
    second_inverse_smooth := S.second_identify.euclideanEndInverse_contMDiff _ EB'
    width := w
    width_pos := hwpos
    neck := S.collarChartOfWidth w hw1
    neck_source := rfl
    neck_smooth := S.collarChartOfWidth_contMDiffOn w hw1
    neck_inverse_smooth := S.collarChartOfWidth_symm_contMDiffOn w hw1
    negative_mem := ?_
    positive_mem := ?_
    negative_eq := ?_
    positive_eq := ?_
    central_disjoint := S.central_not_mem
    cover := S.cover }
  · intro q s hs
    exact S.negative_mem_first q ⟨by linarith [hs.1], hs.2⟩
  · intro q s hs
    exact S.positive_mem_second q ⟨hs.1, by linarith [hs.2]⟩
  · intro q s hs
    have hfull : s ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith [hs.1], hs.2⟩
    have hsmall : -s ∈ Ioo 0 epsilonA := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    let a : (⟨S.first_ball.closedBallᶜ, S.first_ball.closedBall_closed.isOpen_compl⟩ :
        TopologicalSpace.Opens A.carrier) :=
      ⟨S.first_ball.map ((1 + (-s)) • q.val), S.first_ball.radial_mem_complement q
        ⟨by linarith [hsmall.1], by linarith [hsmall.2]⟩⟩
    change a0 (S.collar (q, s)) = (-1 / s) • q.val
    rw [S.negative_gluing q s hfull]
    change S.first_identify.euclideanEndChart _ EA S.first_open
      (S.first_identify.map a.val) = (-1 / s) • q.val
    rw [S.first_identify.euclideanEndChart_map _ EA S.first_open a]
    have h := hEA q (-s) hsmall
    change EA a = (1 / (-s)) • q.val at h
    rw [h]
    congr 1
    simp [div_eq_mul_inv]
  · intro q s hs
    have hfull : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
    have hsmall : s ∈ Ioo 0 epsilonB := ⟨hs.1, by linarith [hs.2]⟩
    have hrecip : (2 : ℝ) ≤ 1 / s := by
      apply (le_div_iff₀ hs.1).mpr
      linarith [hs.2]
    let a : (⟨S.second_ball.closedBallᶜ, S.second_ball.closedBall_closed.isOpen_compl⟩ :
        TopologicalSpace.Opens B.carrier) :=
      ⟨S.second_ball.map ((1 + s) • (S.sphere_gluing q).val),
        S.second_ball.radial_mem_complement (S.sphere_gluing q)
          ⟨by linarith [hsmall.1], by linarith [hsmall.2]⟩⟩
    change a1 (S.collar (q, s)) = (1 / s) • q.val
    rw [S.positive_gluing q s hfull]
    change S.second_identify.euclideanEndChart _ EB' S.second_open
      (S.second_identify.map a.val) = (1 / s) • q.val
    rw [S.second_identify.euclideanEndChart_map _ EB' S.second_open a]
    change radialDiffeomorph D q0 (a := 1) (b := 2) (by norm_num) (by norm_num)
      (EB a) = (1 / s) • q.val
    have h := hEB (S.sphere_gluing q) s hsmall
    change EB a = (1 / s) • (S.sphere_gluing q).val at h
    rw [h, radialDiffeomorph_pos_smul D q0 (S.sphere_gluing q)
      (a := 1) (b := 2) (by norm_num) (by norm_num) hrecip,
      S.sphere_gluing.symm_apply_apply]

include S EA epsilonA hApos hAlt hEA EB epsilonB hBpos hBlt hEB in

theorem nonempty_sphereDiffeomorph_of_canonicalEnds (hD : DiffSphereIsotopyService) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞) := by
  obtain ⟨D⟩ := hD S.sphere_gluing.symm
  let q0 : UnitTwoSphere := Classical.choice
    (NormedSpace.sphere_nonempty (E := StandardCapSpace).mpr zero_le_one).coe_sort
  let v : ThreeSphere := Classical.choice
    (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4)).mpr zero_le_one).coe_sort
  exact ⟨(S.canonicalEndChartData EA epsilonA hApos hAlt hEA EB epsilonB hBpos hBlt hEB
    q0 D).sphereDiffeomorph q0 v⟩

end PoincareConjecture.SmoothConnectedSumData
