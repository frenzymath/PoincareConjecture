import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.TransverseProjectionInverseBound
import PoincareConjecture.Proofs.M76.Mathlib.VariableProjectionDerivative

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_variableProjection_chart (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces,
      t ⊆ u ∧ u.card = Module.finrank ℝ F + 1)
    {s : Finset E} (hs : s ∈ K.faces)
    (hpair : ∀ t ∈ K.faces, s ⊆ t → t.card = Module.finrank ℝ F →
      K.HasTwoFullCofaces (Module.finrank ℝ F) t)
    (a : K.space) (ha : (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (Q : E → E →L[ℝ] F) (hQ : ContDiffAt ℝ ∞ Q (a : E))
    (J : F →L[ℝ] E) (hJ : Function.RightInverse J (Q a))
    (htrans : (Q a).ker.IsSecantTransverse (K.closedFaceStar s).space)
    {V : Set K.space} (hV : V ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph K.space F, a ∈ e.source ∧
      e.source ⊆ (Subtype.val ⁻¹' (K.closedFaceStar s).space) ∩ V ∧
      ∀ x ∈ e.source, e x = Q x ((x : E) - a) := by
  let S : Set K.space := Subtype.val ⁻¹' (K.closedFaceStar s).space
  have hS : S ∈ 𝓝 a := K.closedFaceStar_mem_nhds_of_intrinsicInterior hfinite hs a ha
  obtain ⟨L, hL⟩ := (Q a).exists_inverse_secant_bound_of_ker_transverse J hJ htrans
  have hsub : (K.closedFaceStar s).space ⊆ K.space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    exact convexHull_subset_space ht.1 hxt
  have himage : (fun x : K.space => Q a x) '' S = Q a '' (K.closedFaceStar s).space := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  have hinterior : Q a a ∈ interior ((fun x : K.space => Q a x) '' S) := by
    rw [himage]
    exact K.mem_interior_linearImage_closedFaceStar hfinite hpure hs hpair ha (Q a)
      (htrans.injOn (Q a) rfl)
  exact hQ.hasStrictFDerivAt_variable_projection.exists_carrier_openPartialHomeomorph
    hS (fun x hx y hy => hL x hx y hy) hinterior hV

end Geometry.SimplicialComplex
