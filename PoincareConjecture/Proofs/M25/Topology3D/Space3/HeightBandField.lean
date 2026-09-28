import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization

set_option autoImplicit false

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_compact_height_band_field {S U : Set E}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (ρ : E → ℝ) (hρ : ContDiffOn ℝ ∞ ρ U)
    (hn : ∀ y ∈ U, gradient ρ y ≠ 0)
    (u : E) (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hreg : ∀ y ∈ S, ⟪u, y⟫_ℝ ∈ tsupport b →
      tangentHeightVector (gradient ρ y) u ≠ 0) :
    ∃ F : E → E, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ tsupport F ⊆ U ∧
      (∀ y, fderiv ℝ ρ y (F y) = 0) ∧
      ∀ y ∈ S, ⟪u, F y⟫_ℝ = b ⟪u, y⟫_ℝ := by
  let H := InnerProductSpace.toDual ℝ E u
  let W : E → E := fun y => tangentHeightVector (gradient ρ y) u
  let V : Set E := U ∩ W ⁻¹' ({0} : Set E)ᶜ
  have hW : ContDiffOn ℝ ∞ W U := tangentHeightVector_contDiffOn (gradient ρ)
    (contDiffOn_gradient_of_isOpen hU ρ hρ) hn u
  have hV : IsOpen V :=
    hW.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  let K : Set E := S ∩ H ⁻¹' tsupport b
  have hK : IsCompact K := hS.inter_right ((isClosed_tsupport b).preimage H.continuous)
  have hKV : K ⊆ V := fun y hy => ⟨hSU hy.1, hreg y hy.1 hy.2⟩
  obtain ⟨χ, hχ, hχc, hχV, hχnear, _⟩ := exists_compact_smooth_cutoff hK hV hKV
  let Z : E → E := fun y => tangentHeightField (gradient ρ y) u
  have hZ : ContDiffOn ℝ ∞ Z V := tangentHeightField_contDiffOn (gradient ρ)
    ((contDiffOn_gradient_of_isOpen hU ρ hρ).mono inter_subset_left)
    (fun y hy => hn y hy.1) u (fun _ hy => hy.2)
  let F : E → E := fun y => χ y • (b (H y) • Z y)
  have hF : ContDiff ℝ ∞ F := contDiff_cutoff_smul hV χ hχ hχV _
    (((hb.comp H.contDiff).contDiffOn).smul hZ)
  refine ⟨F, hF, hχc.smul_right,
    (tsupport_smul_subset_left χ _).trans (hχV.trans inter_subset_left), ?_, ?_⟩
  · intro y
    by_cases hy : χ y = 0
    · simp only [F, hy, zero_smul, map_zero]
    · have hyV := hχV (subset_tsupport χ hy)
      change fderiv ℝ ρ y (χ y • (b (H y) • tangentHeightField (gradient ρ y) u)) = 0
      rw [map_smul, map_smul,
        tangentHeightField_defining_derivative ρ y u (hn y hyV.1), smul_zero, smul_zero]
  · intro y hyS
    by_cases hyb : b (H y) = 0
    · change ⟪u, χ y • (b (H y) • Z y)⟫_ℝ = b (H y)
      rw [hyb, zero_smul, smul_zero, inner_zero_right]
    · have hyK : y ∈ K := ⟨hyS, subset_tsupport b hyb⟩
      have hχy : χ y = 1 := subset_of_mem_nhdsSet hχnear hyK
      change ⟪u, χ y • (b (H y) • tangentHeightField (gradient ρ y) u)⟫_ℝ = b (H y)
      rw [hχy, one_smul, inner_smul_right,
        tangentHeightField_height _ _ (hn y (hSU hyS)) (hreg y hyS hyK.2), mul_one]

end PoincareConjecture.M25.Topology3D
