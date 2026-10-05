import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic
import PoincareLib.Topology.Manifold.EmbeddedSphere.Chart.Complement

/-!
# The nonempty complement of the embedded sphere

The sphere has dimension two and the ambient manifold has dimension three,
so the smooth embedding has dense complement. This proves the nonemptiness
part of the frozen `SeparatingSphere` predicate used in the separation repair
for Morgan--Tian Proposition 15.12 and Remark 15.13, printed p. 365.
See derivation 01 in `proof-work/tasks/M53/derivations/`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- The complement of a smoothly embedded two-sphere in a three-manifold
is dense, by positive codimension. Source: derivation 01, for Morgan--Tian
Proposition 15.12 and Remark 15.13, printed p. 365. -/
theorem sphere_dense_compl (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    Dense (Set.range S.sphere)ᶜ := by
  apply S.smooth_embedding.dense_compl_range
  simp

/-- The sphere has nonempty complement, as required separately by
`SeparatingSphere`. Source: derivation 01, nonemptiness step for
Morgan--Tian Proposition 15.12 and Remark 15.13, printed p. 365. -/
theorem sphere_complement_nonempty [Nonempty M]
    (S : SmoothEmbeddedNullHomotopicSphere (M := M)) :
    (Set.univ \ Set.range S.sphere).Nonempty := by
  simpa only [Set.compl_eq_univ_sdiff] using (sphere_dense_compl S).nonempty

end PoincareMT.Topology.EmbeddedSphere
