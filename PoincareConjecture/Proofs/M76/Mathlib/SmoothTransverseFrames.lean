import PoincareConjecture.Proofs.M76.Mathlib.GeometricFrameField
import PoincareConjecture.Proofs.M76.Mathlib.TransversePlaneDimension










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Geometry.EuclideanSubspace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem IsSmoothLeafFieldOn.exists_transverse_frame_neighborhood
    {P : E → EuclideanSubspace E} {U S : Set E} (hP : IsSmoothLeafFieldOn P U)
    (hU : IsOpen U) (hSU : S ⊆ U) (J : F →L[ℝ] E) (hJ : Function.Injective J)
    (hdim : ∀ x ∈ U,
      Module.finrank ℝ (P x).subspace + Module.finrank ℝ F = Module.finrank ℝ E)
    (A : Set E)
    (hdisjoint : ∀ L : Submodule ℝ E, L.IsSecantTransverse A → Disjoint J.range L)
    (htrans : ∀ x ∈ S, (P x).subspace.IsSecantTransverse A) :
    ∃ V : Set E, IsOpen V ∧ S ⊆ V ∧ V ⊆ U ∧
      ∃ Q : E → E →L[ℝ] F, ContDiffOn ℝ ∞ Q V ∧
        (∀ x ∈ V, Function.RightInverse J (Q x) ∧ (Q x).ker = (P x).subspace ∧
          (Q x).ker.IsSecantTransverse A) ∧
        ∀ x ∈ V, ∀ᶠ y in 𝓝 x, y - x ∈ (Q x).ker → Q y = Q x := by
  let V : Set E := U ∩ P ⁻¹' {L : EuclideanSubspace E | L.subspace.IsSecantTransverse A}
  have hV : IsOpen V := hP.continuousOn.isOpen_inter_preimage hU (isOpen_isSecantTransverse A)
  have hSV : S ⊆ V := fun x hx => ⟨hSU hx, htrans x hx⟩
  have hcompl (x : E) (hx : x ∈ V) : IsCompl J.range (P x).subspace := by
    apply (Submodule.isCompl_iff_disjoint J.range (P x).subspace ?_).mpr
    · exact hdisjoint _ hx.2
    · have hfd : Module.finrank ℝ J.range = Module.finrank ℝ F :=
        LinearMap.finrank_range_of_inj hJ
      have hxd := hdim x hx.1
      omega
  obtain ⟨Q, hQ, hspec, hleaf⟩ :=
    (hP.mono (show V ⊆ U from inter_subset_left)).exists_frameRepresentation J hJ hcompl
  refine ⟨V, hV, hSV, inter_subset_left, Q, hQ, ?_, hleaf⟩
  intro x hx
  refine ⟨(hspec x hx).1, (hspec x hx).2, ?_⟩
  rw [(hspec x hx).2]
  exact hx.2

end Geometry.EuclideanSubspace
