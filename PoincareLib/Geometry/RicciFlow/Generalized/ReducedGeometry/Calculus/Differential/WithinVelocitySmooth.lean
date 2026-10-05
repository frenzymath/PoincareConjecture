import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth within derivatives applied to a fixed source vector

The velocity-regularity step in Morgan-Tian Lemma 6.8, pp. 108-109.
Unique derivatives on the source set suffice; no open-domain extension
is used to prove smoothness of the bundled tangent derivative.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

variable {𝕜 E E' H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E' H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {U : Set E} {α : E → M} {m k : ℕ∞ω}

/-- Applying the within derivative to a constant source vector preserves
smoothness with one derivative lost, as used in Lemma 6.8, pp. 108-109. -/
theorem ContMDiffOn.contMDiffOn_mfderivWithin_const_apply
    (hα : ContMDiffOn (𝓘(𝕜, E)) I m α U) (hU : UniqueDiffOn 𝕜 U)
    (v : E) (hkm : k + 1 ≤ m) :
    ContMDiffOn (𝓘(𝕜, E)) I.tangent k
      (fun s => Bundle.TotalSpace.mk' E' (α s)
        (mfderivWithin (𝓘(𝕜, E)) I α U s v)) U := by
  have hv : ContMDiff (𝓘(𝕜, E)) (𝓘(𝕜, E)).tangent k
      (fun s : E => (⟨s, v⟩ : TangentBundle (𝓘(𝕜, E)) E)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  exact (hα.contMDiffOn_tangentMapWithin hkm hU.uniqueMDiffOn).comp
    hv.contMDiffOn (fun _ hs => hs)
