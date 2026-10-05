import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance

/-!
The dense-time canonical-neighborhood vocabulary is shared by the
bounded-distance theory and the `Generalized.DenseTime` compatibility names.
It depends only on the earlier-time bounded-distance definitions.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Full canonical control on one actual slice above an absolute scalar cutoff. -/
def generalizedSliceStrongCanonicalNeighborhoods
    (F : GeneralizedRicciFlowData.{u}) (epsilon C Q s : ℝ) : Prop :=
  ∀ y : (F.slice s).carrier, Q ≤ F.scalar ⟨s, y⟩ →
    Nonempty (GeneralizedCanonicalControl (F := F) s y epsilon C)

/-- One whole good slice is available arbitrarily close from the left to
every earlier included time. The inclusive endpoint also tests an included
minimum; the good time is chosen before its spatial points. -/
def generalizedEarlierDenseStrongCanonicalNeighborhoods
    (F : GeneralizedRicciFlowData.{u})
    (epsilon C t : ℝ) (x : (F.slice t).carrier) : Prop :=
  ∀ s, s ∈ F.interval → s ≤ t → ∀ a, a < s →
    ∃ u, u ∈ F.interval ∧ a < u ∧ u ≤ s ∧
      generalizedSliceStrongCanonicalNeighborhoods F epsilon C
        (4 * F.scalar ⟨t, x⟩) u

theorem generalizedEarlierStrongCanonicalNeighborhoods.left_dense
    {F : GeneralizedRicciFlowData.{u}} {epsilon C t : ℝ}
    {x : (F.slice t).carrier}
    (h : generalizedEarlierStrongCanonicalNeighborhoods F epsilon C t x) :
    generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t x := by
  intro s hs hst a has
  exact ⟨s, hs, has, le_rfl, h s hs hst⟩

end PoincareMT
