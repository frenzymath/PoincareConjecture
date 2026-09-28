import PoincareConjecture.Proofs.M76.Mathlib.FiniteComplexLeafChart
import PoincareConjecture.Proofs.M76.Mathlib.SmoothTransverseFrames
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFaceTransversality










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]






theorem exists_chart_of_smoothLeafField (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces,
      t ⊆ u ∧ u.card = Module.finrank ℝ F + 1)
    {s : Finset E} (hs : s ∈ K.faces)
    (hpair : ∀ t ∈ K.faces, s ⊆ t → t.card = Module.finrank ℝ F →
      K.HasTwoFullCofaces (Module.finrank ℝ F) t)
    (a : K.space) (ha : (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {P : E → EuclideanSubspace E} {U : Set E}
    (hP : EuclideanSubspace.IsSmoothLeafFieldOn P U) (hU : IsOpen U) (haU : (a : E) ∈ U)
    (hdim : ∀ y ∈ U,
      Module.finrank ℝ (P y).subspace + Module.finrank ℝ F = Module.finrank ℝ E)
    (htrans : (P a).subspace.IsSecantTransverse (K.closedFaceStar s).space) :
    ∃ e : OpenPartialHomeomorph K.space F, ∃ b : F →ᴬ[ℝ] E, ∃ Q : E → E →L[ℝ] F,
      a ∈ e.source ∧
      (∀ z ∈ e.target, ContDiffAt ℝ ∞ Q (b z)) ∧
      ∀ y ∈ e.source, Function.RightInverse b.contLinear (Q y) ∧
        (Q y).ker = (P y).subspace ∧ Q (b (e y)) = Q y ∧
        b (e y) - y ∈ (P y).subspace := by
  obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
  let T := (affineSpan ℝ (t : Set E)).direction
  let A : F ≃L[ℝ] T := ContinuousLinearEquiv.ofFinrankEq
    (K.finrank_faceDirection_of_card ht htcard).symm
  let J : F →L[ℝ] E := T.subtypeL.comp A.toContinuousLinearMap
  have hJ : Function.Injective J := Subtype.val_injective.comp A.injective
  have hJrange : J.range ≤ T := by
    rintro x ⟨z, rfl⟩
    exact (A z).property
  have htstar : t ∈ (K.closedFaceStar s).faces :=
    ⟨ht, by simpa only [Finset.union_eq_right.mpr hst] using ht⟩
  have hdisjoint : ∀ L : Submodule ℝ E,
      L.IsSecantTransverse (K.closedFaceStar s).space → Disjoint J.range L := by
    intro L hL
    exact ((K.closedFaceStar s).disjoint_faceDirection_of_isSecantTransverse htstar hL).mono_left
      hJrange
  obtain ⟨V, hV, haV, _, Q, hQ, hspec, hleaf⟩ :=
    hP.exists_transverse_frame_neighborhood hU (singleton_subset_iff.mpr haU) J hJ hdim
      (K.closedFaceStar s).space hdisjoint (by simpa using htrans)
  have haV' : (a : E) ∈ V := haV (mem_singleton _)
  obtain ⟨e, hae, heV, he⟩ := K.exists_leafProjection_chart hfinite hpure hs hpair a ha
    hV haV' Q hQ J (fun y hy => (hspec y hy).1) hleaf (hspec a haV').2.2
  let b : F →ᴬ[ℝ] E := ContinuousAffineMap.const ℝ F (a : E) + J.toContinuousAffineMap
  have hb (z : F) : b z = (a : E) + J z := rfl
  have hblinear : b.contLinear = J := by
    ext z
    change (0 : E) + J z = J z
    exact zero_add _
  refine ⟨e, b, Q, hae, ?_, fun y hy => ?_⟩
  · intro z hz
    have hy := e.map_target hz
    have h := (he (e.symm z) hy).2.1
    rw [e.right_inv hz] at h
    exact hQ.contDiffAt (hV.mem_nhds h)
  · obtain ⟨_, hslice, heq, hmem⟩ := he y hy
    obtain ⟨hnorm, hker, _⟩ := hspec y (heV hy)
    refine ⟨?_, hker, heq, ?_⟩
    · rwa [hblinear]
    · rwa [← hker]

end Geometry.SimplicialComplex
