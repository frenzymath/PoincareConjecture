import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Dense

/-!
# Canonical control on selected slices

Adapters for the same-time and left-dense forms of Morgan--Tian
Theorem 10.2, printed pp. 245-246, as specified by the regular-time
canonical-boundary review of 2026-09-18. Good times are chosen before
spatial points, and an included minimum retains its full-slice condition.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Raising the scalar cutoff retains control on the same actual slice.
See Morgan--Tian Theorem 10.2, printed pp. 245-246. -/
theorem generalizedSliceStrongCanonicalNeighborhoods.mono_cutoff
    {F : GeneralizedRicciFlowData.{u}} {epsilon C Q Q' s : ℝ}
    (h : generalizedSliceStrongCanonicalNeighborhoods F epsilon C Q s)
    (hQ : Q ≤ Q') : generalizedSliceStrongCanonicalNeighborhoods F epsilon C Q' s := by
  intro y hy
  exact h y (hQ.trans hy)

/-- Earlier canonical control includes the tested slice. This is the
specialization used in the printed corollary of Theorem 10.2, p. 246. -/
theorem generalizedEarlierStrongCanonicalNeighborhoods.at_time
    {F : GeneralizedRicciFlowData.{u}} {epsilon C t : ℝ}
    {x : (F.slice t).carrier}
    (h : generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x)
    (ht : t ∈ F.interval) :
    generalizedSliceStrongCanonicalNeighborhoods F epsilon C (4 * F.scalar ⟨t, x⟩) t :=
  h t ht le_rfl

/-- At an included minimum, left-dense whole-slice control controls that
very slice. See the 2026-09-18 regular-time boundary review, M28 section. -/
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

/-- Rebasing at an earlier point with larger scalar curvature only raises
the cutoff and shortens the tested past. This preserves one common good
slice, as required in the dense-time argument of the boundary review. -/
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

end PoincareMT
