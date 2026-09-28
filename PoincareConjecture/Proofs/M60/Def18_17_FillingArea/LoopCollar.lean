import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.CollarRegularity
import PoincareConjecture.Proofs.M58.Cor18_28_DiskExtension











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



noncomputable def m60LoopCollar (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M)) (z : LoopPlane) : M :=
  C (1 - diskTimeProfile ‖z‖, γ₁.extension (radialNormalization z),
    γ₀.extension (radialNormalization z))



theorem m60LoopCollar_inner (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M)) (h0 : ∀ p q, C (0, p, q) = q)
    {z : LoopPlane} (hz : ‖z‖ ≤ 1 / 2) :
    m60LoopCollar C γ₀ γ₁ z = γ₀.extension (radialNormalization z) := by
  rw [m60LoopCollar, diskTimeProfile_eq_one (norm_nonneg z) hz, sub_self, h0]



theorem m60LoopCollar_boundary (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M))
    (h1 : ∀ z : LoopCircle, C (1, γ₁ z, γ₀ z) = γ₁ z) (z : LoopCircle) :
    m60LoopCollar C γ₀ γ₁ z = γ₁ z := by
  rw [m60LoopCollar, z.property, diskTimeProfile_one, sub_zero,
    radialNormalization_of_norm_eq_one z.property, γ₀.boundary, γ₁.boundary, h1]




theorem m60LoopCollar_contMDiffAt (C : ℝ × (M × M) → M)
    (γ₀ γ₁ : C1FreeLoopSpace (M := M))
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, γ₁ z, γ₀ z))
    {z : LoopPlane} (hz : z ≠ 0) : ContMDiffAt (𝓡 2) (𝓡 3) 1 (m60LoopCollar C γ₀ γ₁) z := by
  let q : LoopCircle := ⟨radialNormalization z, norm_radialNormalization hz⟩
  have ht : 1 - diskTimeProfile ‖z‖ ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨h0, h1⟩ := diskTimeProfile_mem_Icc ‖z‖
    exact ⟨sub_nonneg.mpr h1, by linarith⟩
  have htime : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) 1
      (fun w : LoopPlane => 1 - diskTimeProfile ‖w‖) z :=
    ((contDiffAt_const.sub (contDiff_diskTimeProfile.contDiffAt.comp z
      (contDiffAt_norm ℝ hz))).of_le (by simp)).contMDiffAt
  have hinput := htime.prodMk
    ((contMDiffAt_radial_extension γ₁ hz).prodMk (contMDiffAt_radial_extension γ₀ hz))
  exact (hC _ ht q).comp_of_eq hinput (by
    change (1 - diskTimeProfile ‖z‖, γ₁.extension q.val, γ₀.extension q.val) = _
    rw [γ₀.boundary, γ₁.boundary])




theorem m60LoopCollar_matches_disk (g : RiemannianMetric 3 M)
    {γ₀ γ₁ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ₀)
    (hD : ∀ z : LoopCircle, D.map z = γ₀ z)
    (C : ℝ × (M × M) → M) (h0 : ∀ p q, C (0, p, q) = q)
    {rho : ℝ} (hrho : 0 < rho) (hrho2 : rho ≤ 1 / 2)
    {z : LoopPlane} (hz : ‖z‖ = rho) :
    D.map (rho⁻¹ • z) = m60LoopCollar C γ₀ γ₁ z := by
  have hz0 : z ≠ 0 := fun h => by simpa [h] using hz.trans_gt hrho
  let q : LoopCircle := ⟨radialNormalization z, norm_radialNormalization hz0⟩
  rw [m60LoopCollar_inner C γ₀ γ₁ h0 (hz.trans_le hrho2)]
  have hrad : radialNormalization z = rho⁻¹ • z := by rw [radialNormalization, hz]
  rw [← hrad]
  exact (hD q).trans (γ₀.boundary q).symm

end PoincareConjecture
