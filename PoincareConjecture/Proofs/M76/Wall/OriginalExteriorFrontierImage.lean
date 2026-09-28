import Mathlib.Data.Set.Function
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Closure











set_option autoImplicit false

open Set

namespace PoincareConjecture.M76




theorem original_exterior_frontier_images
    {X E : Type*} [TopologicalSpace X] {C L R : Set X}
    (hL : IsClosed L) (hLC : L ⊆ C) {F : X → E} {g : E → X}
    (hgF : LeftInvOn g F C) {N D : Set E}
    (hN : N = F '' (C \ interior L)) (hD : D = F '' frontier L)
    {h : E → ℝ} {beta : ℝ}
    (hnew : frontier R = ((C \ interior L) ∩ {y | h (F y) = beta}) ∪
      (frontier L ∩ {y | beta ≤ h (F y)}))
    (hunion : frontier (L ∪ R) = (frontier L ∩ {y | h (F y) ≤ beta}) ∪
      ((C \ interior L) ∩ {y | h (F y) = beta})) :
    frontier R = g '' ((N ∩ {z | h z = beta}) ∪ (D ∩ {z | beta ≤ h z})) ∧
      frontier (L ∪ R) =
        g '' ((D ∩ {z | h z ≤ beta}) ∪ (N ∩ {z | h z = beta})) := by
  have hfilter (S : Set X) (hSC : S ⊆ C) (T : Set E) :
      g '' (F '' S ∩ T) = S ∩ F ⁻¹' T := by
    have hleft : LeftInvOn g F S := hgF.mono hSC
    have hright : LeftInvOn F g (F '' S) := hleft.rightInvOn_image
    calc
      g '' (F '' S ∩ T) = g '' (T ∩ F '' S) := by rw [inter_comm]
      _ = F ⁻¹' T ∩ g '' (F '' S) := hright.image_inter'
      _ = S ∩ F ⁻¹' T := by rw [hleft.image_image, inter_comm]
  have hlevel : g '' (N ∩ {z | h z = beta}) =
      (C \ interior L) ∩ {y | h (F y) = beta} := by
    rw [hN]
    exact hfilter _ sdiff_subset _
  have hhigh : g '' (D ∩ {z | beta ≤ h z}) =
      frontier L ∩ {y | beta ≤ h (F y)} := by
    rw [hD]
    exact hfilter _ (hL.frontier_subset.trans hLC) _
  have hlow : g '' (D ∩ {z | h z ≤ beta}) =
      frontier L ∩ {y | h (F y) ≤ beta} := by
    rw [hD]
    exact hfilter _ (hL.frontier_subset.trans hLC) _
  constructor
  · rw [image_union, hlevel, hhigh]
    exact hnew
  · rw [image_union, hlow, hlevel]
    exact hunion

end PoincareConjecture.M76
