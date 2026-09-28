import PoincareConjecture.Definitions.M28BoundedDistance

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem generalizedSliceStrongCanonicalNeighborhoods.mono_cutoff
    {F : GeneralizedRicciFlowData.{u}} {epsilon C Q Q' s : ℝ}
    (h : generalizedSliceStrongCanonicalNeighborhoods F epsilon C Q s)
    (hQ : Q ≤ Q') : generalizedSliceStrongCanonicalNeighborhoods F epsilon C Q' s := by
  intro y hy
  exact h y (hQ.trans hy)

theorem generalizedEarlierStrongCanonicalNeighborhoods.at_time
    {F : GeneralizedRicciFlowData.{u}} {epsilon C t : ℝ}
    {x : (F.slice t).carrier}
    (h : generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x)
    (ht : t ∈ F.interval) :
    generalizedSliceStrongCanonicalNeighborhoods F epsilon C (4 * F.scalar ⟨t, x⟩) t :=
  h t ht le_rfl

theorem generalizedEarlierDenseStrongCanonicalNeighborhoods.at_minimum
    {F : GeneralizedRicciFlowData.{u}} {epsilon C t : ℝ}
    {x : (F.slice t).carrier}
    (h : generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x)
    (ht : t ∈ F.interval) (hmin : ∀ s ∈ F.interval, t ≤ s) :
    generalizedSliceStrongCanonicalNeighborhoods F epsilon C (4 * F.scalar ⟨t, x⟩) t := by
  obtain ⟨s, hs, _, hst, hslice⟩ := h t ht le_rfl (t - 1) (by linarith)
  have hst' : s = t := le_antisymm hst (hmin s hs)
  subst s
  exact hslice

theorem generalizedEarlierDenseStrongCanonicalNeighborhoods.rebase
    {F : GeneralizedRicciFlowData.{u}} {epsilon C s t : ℝ}
    {x : (F.slice t).carrier} {y : (F.slice s).carrier}
    (h : generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x)
    (hst : s ≤ t) (hscalar : F.scalar ⟨t, x⟩ ≤ F.scalar ⟨s, y⟩) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C s y := by
  intro v hv hvs a hav
  obtain ⟨w, hw, haw, hwv, hslice⟩ := h v hv (hvs.trans hst) a hav
  refine ⟨w, hw, haw, hwv, hslice.mono_cutoff ?_⟩
  exact mul_le_mul_of_nonneg_left hscalar (by norm_num)

end PoincareConjecture
