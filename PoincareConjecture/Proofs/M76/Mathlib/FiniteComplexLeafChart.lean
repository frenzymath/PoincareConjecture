import PoincareConjecture.Proofs.M76.Mathlib.FiniteComplexProjectionChart
import PoincareConjecture.Proofs.M76.Mathlib.NormalizedProjectionLeaves

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_leafProjection_chart (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces,
      t ⊆ u ∧ u.card = Module.finrank ℝ F + 1)
    {s : Finset E} (hs : s ∈ K.faces)
    (hpair : ∀ t ∈ K.faces, s ⊆ t → t.card = Module.finrank ℝ F →
      K.HasTwoFullCofaces (Module.finrank ℝ F) t)
    (a : K.space) (ha : (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {U : Set E} (hU : IsOpen U) (haU : (a : E) ∈ U)
    (Q : E → E →L[ℝ] F) (hQ : ContDiffOn ℝ ∞ Q U)
    (J : F →L[ℝ] E) (hJ : ∀ y ∈ U, Function.RightInverse J (Q y))
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ (Q y).ker → Q z = Q y)
    (htrans : (Q a).ker.IsSecantTransverse (K.closedFaceStar s).space) :
    ∃ e : OpenPartialHomeomorph K.space F, a ∈ e.source ∧
      e.source ⊆ Subtype.val ⁻¹' U ∧
      ∀ y ∈ e.source, e y = Q y ((y : E) - a) ∧
        (a : E) + J (e y) ∈ U ∧ Q ((a : E) + J (e y)) = Q y ∧
        (a : E) + J (e y) - y ∈ (Q y).ker := by
  obtain ⟨W, hW, haW, hWU, hspec⟩ :=
    hQ.continuousOn.exists_normalizedProjection_leaf_neighborhood hU haU J hJ hleaf
  have hWpre : (Subtype.val ⁻¹' W : Set K.space) ∈ 𝓝 a :=
    (hW.preimage continuous_subtype_val).mem_nhds haW
  obtain ⟨e, hae, hesub, he⟩ := K.exists_variableProjection_chart hfinite hpure hs hpair a ha Q
    (hQ.contDiffAt (hU.mem_nhds haU)) J (hJ a haU) htrans hWpre
  refine ⟨e, hae, fun y hy => hWU (hesub hy).2, fun y hy => ⟨he y hy, ?_⟩⟩
  rw [he y hy]
  exact hspec y (hesub hy).2

end Geometry.SimplicialComplex
