import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CollarKernelInjectivity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Collars.SupportedRim









set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem fundamentalGroup_whole_phase_injective_of_kernel_control
    {E X Y : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    {R : Set X} (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (q : C(X, Y)) (hphase : ∀ z ∈ K ×ˢ Icc (-r) r, q (c z) = q (c (z.1, 0)))
    (theta : Y) {N : Set X} (hSN : R ∩ q ⁻¹' {theta} ⊆ N)
    (hkernel : ∀ (x : ↥((R ∩ q ⁻¹' {theta}) \ frontier R))
      (gamma : FundamentalGroup ↥((R ∩ q ⁻¹' {theta}) \ frontier R) x),
      FundamentalGroup.map (ContinuousMap.inclusion (sdiff_subset.trans hSN)) x gamma = 1 →
      FundamentalGroup.map (ContinuousMap.inclusion sdiff_subset) x gamma = 1) :
    ∀ x : ↥(R ∩ q ⁻¹' {theta}),
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x) := by
  let S := R ∩ q ⁻¹' {theta}
  let M := S \ frontier R
  let B := (Subtype.val : S → X) ⁻¹' frontier R
  let f : C(S, N) := ContinuousMap.inclusion hSN
  let incl : C(↥Bᶜ, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let m : C(↥Bᶜ, M) := ⟨fun z => ⟨z.val.val, z.val.property, z.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hker (x : ↥Bᶜ) (gamma : FundamentalGroup ↥Bᶜ x)
      (hg : FundamentalGroup.map (f.comp incl) x gamma = 1) :
      FundamentalGroup.map incl x gamma = 1 := by
    have h := hkernel (m x) (FundamentalGroup.map m x gamma)
    have hN : FundamentalGroup.map (ContinuousMap.inclusion (sdiff_subset.trans hSN))
        (m x) (FundamentalGroup.map m x gamma) = 1 := by
      rw [← MonoidHom.comp_apply, ← FundamentalGroup.map_comp]
      exact hg
    have hS := h hN
    rw [← MonoidHom.comp_apply, ← FundamentalGroup.map_comp] at hS
    exact hS
  intro x
  obtain ⟨hKt, cS, _, hcS, hiS, hoS, hzS⟩ :=
    exists_phase_rim_collar hK hr c hc hi ho hzero hside q hphase theta x
  have h := fundamentalGroup_map_injective_of_collar_kernel_control hKt hr cS hcS hiS hoS f
  rw [hzS] at h
  exact h hker x

end Poincare.Topology
