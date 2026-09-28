import PoincareConjecture.Proofs.M38.AnnulusReparametrization
import PoincareConjecture.Proofs.M38.ShortCollar









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A B C : GeneralizedSliceCarrier.{u}}
  (D₀ : SurgeryBallEmbedding A) (D₁ : SurgeryBallEmbedding B)
  {U V : Set C.carrier} (hU : IsOpen U) (hV : IsOpen V)
  (E₀ : SurgeryRegionEquivalence A C D₀.closedBallᶜ U)
  (E₁ : SurgeryRegionEquivalence B C D₁.closedBallᶜ V)
  (hUV : Disjoint U V)
  (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
  (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace C.carrier ∞)
  {ε : ℝ} (hc : c.source = Set.univ ×ˢ Set.Ioo (-ε) ε)
  (hneg : ∀ z : UnitTwoSphere, ∀ s ∈ Set.Ioo (-ε) 0,
    c (z, s) = E₀.map (D₀.map ((1 - s) • z.val)))
  (hpos : ∀ z : UnitTwoSphere, ∀ s ∈ Set.Ioo (0 : ℝ) ε,
    c (z, s) = E₁.map (D₁.map ((1 + s) • (phi z).val)))
  (hcentral : Disjoint (c '' (Set.univ ×ˢ ({0} : Set ℝ))) (U ∪ V))
  (hcover : U ∪ V ∪ (c '' (Set.univ ×ˢ ({0} : Set ℝ))) = Set.univ)



noncomputable def shortCollarConnectedSumData {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (haε : a ≤ ε) : SmoothConnectedSumData A B C := by
  refine {
    first_ball := annulusReparametrizedBall ha ha1 D₀
    second_ball := annulusReparametrizedBall ha ha1 D₁
    first_region := U
    second_region := V
    first_open := hU
    second_open := hV
    first_identify := {
      map := E₀.map
      inverse := E₀.inverse
      map_image := by rw [annulusReparametrizedBall_closedBall]; exact E₀.map_image
      inverse_image := by rw [annulusReparametrizedBall_closedBall]; exact E₀.inverse_image
      left_inverse := by rw [annulusReparametrizedBall_closedBall]; exact E₀.left_inverse
      right_inverse := E₀.right_inverse
      map_smooth := by rw [annulusReparametrizedBall_closedBall]; exact E₀.map_smooth
      inverse_smooth := E₀.inverse_smooth }
    second_identify := {
      map := E₁.map
      inverse := E₁.inverse
      map_image := by rw [annulusReparametrizedBall_closedBall]; exact E₁.map_image
      inverse_image := by rw [annulusReparametrizedBall_closedBall]; exact E₁.inverse_image
      left_inverse := by rw [annulusReparametrizedBall_closedBall]; exact E₁.left_inverse
      right_inverse := E₁.right_inverse
      map_smooth := by rw [annulusReparametrizedBall_closedBall]; exact E₁.map_smooth
      inverse_smooth := E₁.inverse_smooth }
    regions_disjoint := hUV
    sphere_gluing := phi
    collar := shortCollar c a
    collar_inverse := shortCollarInverse c a
    collar_smooth := shortCollar_smooth c ha haε hc
    collar_inverse_smooth := shortCollarInverse_smooth c ha haε hc
    collar_left_inverse := shortCollar_left_inverse c ha haε hc
    collar_right_inverse := shortCollar_right_inverse c ha haε hc
    collar_open := shortCollar_open c ha haε hc
    negative_gluing := ?_
    positive_gluing := ?_
    central_disjoint := by rw [shortCollar_central]; exact hcentral
    cover := by rw [shortCollar_central]; exact hcover }
  · intro z s hs
    change c (z, a * s) = E₀.map
      ((annulusReparametrizedBall ha ha1 D₀).map ((1 - s) • z.val))
    rw [annulusReparametrizedBall_negative ha ha1 D₀ z hs]
    apply hneg
    refine ⟨?_, mul_neg_of_pos_of_neg ha hs.2⟩
    have h := mul_lt_mul_of_pos_left hs.1 ha
    nlinarith
  · intro z s hs
    change c (z, a * s) = E₁.map
      ((annulusReparametrizedBall ha ha1 D₁).map ((1 + s) • (phi z).val))
    rw [annulusReparametrizedBall_positive ha ha1 D₁ (phi z) hs]
    apply hpos
    refine ⟨mul_pos ha hs.1, ?_⟩
    have h := mul_lt_mul_of_pos_left hs.2 ha
    nlinarith

include hU hV E₀ E₁ hUV phi c hc hneg hpos hcentral hcover in


theorem exists_connectedSumData_of_local_gluing (hε : 0 < ε) :
    Nonempty (SmoothConnectedSumData A B C) := by
  let a : ℝ := min (ε / 2) (1 / 8)
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have haε : a ≤ ε := (min_le_left _ _).trans (by linarith)
  exact ⟨shortCollarConnectedSumData D₀ D₁ hU hV E₀ E₁ hUV phi c hc
    hneg hpos hcentral hcover ha ha1 haε⟩

end PoincareConjecture.M38
