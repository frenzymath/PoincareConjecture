import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Implicit
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.Equivalence









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function TopologicalSpace
open scoped Manifold ContDiff Bundle Topology
open Poincare.Geometry.Manifold.RegularLevel

namespace Poincare.Manifold

variable {n : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]


def graphSlab (ε : ℝ) : Opens (ℝ × N) :=
  ⟨Ioo (-ε) ε ×ˢ univ, isOpen_Ioo.prod isOpen_univ⟩

variable {F : ℝ × N → ℝ}
  (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F)

include hF



theorem exists_unique_smooth_level_height
    {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, 0 < deriv (fun r ↦ F (r, y)) s)
    (hleft : ∀ y : N, F (-ε, y) < 0) (hright : ∀ y : N, 0 < F (ε, y)) :
    ∃ u : N → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ y, u y ∈ Ioo (-ε) ε ∧ F (u y, y) = 0) ∧
      ∀ y s, s ∈ Ioo (-ε) ε → (F (s, y) = 0 ↔ s = u y) := by
  classical
  have hcont (y : N) : Continuous (fun s : ℝ ↦ F (s, y)) :=
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  have hmono (y : N) : StrictMonoOn (fun s ↦ F (s, y)) (Icc (-ε) ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hcont y).continuousOn
    simpa only [interior_Icc] using hpos y
  have hex (y : N) : ∃ s ∈ Ioo (-ε) ε, F (s, y) = 0 := by
    obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc (by linarith : -ε ≤ ε)
      (hcont y).continuousOn ⟨(hleft y).le, (hright y).le⟩
    change F (s, y) = 0 at hzero
    refine ⟨s, ⟨?_, ?_⟩, hzero⟩
    · exact lt_of_le_of_ne hs.1 (by intro heq; have := hleft y; rw [heq, hzero] at this; exact this.false)
    · exact lt_of_le_of_ne hs.2 (by intro heq; have := hright y; rw [← heq, hzero] at this; exact this.false)
  choose u hu hzero using hex
  refine ⟨u, ?_, fun y ↦ ⟨hu y, hzero y⟩, ?_⟩
  · intro y
    apply contMDiffAt_of_unique_time_root isOpen_Ioo isOpen_univ hF.contMDiffOn
      (σ := u) (v := deriv (fun r ↦ F (r, y)) (u y))
      (fun z _ ↦ ⟨hu z, hzero z⟩)
      (fun z _ ↦ (hmono z).injOn.mono Ioo_subset_Icc_self) (mem_univ y)
      (hpos y _ (hu y)).ne'
    exact (differentiableAt_of_deriv_ne_zero (hpos y _ (hu y)).ne').hasDerivAt
  · intro y s hs
    constructor
    · intro hzero'
      exact (hmono y).injOn (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self (hu y))
        (hzero'.trans (hzero y).symm)
    · rintro rfl
      exact hzero y

omit [IsManifold (𝓡 n) ∞ N] in


theorem graphSlab_regular {ε : ℝ}
    (hpos : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, 0 < deriv (fun r ↦ F (r, y)) s) :
    ∀ p ∈ graphSlab (N := N) ε,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) F p ≠ 0 := by
  rintro ⟨s, y⟩ hp hzero
  have hcomp := mfderiv_comp s ((hF (s, y)).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk (mdifferentiableAt_const (c := y)))
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r ↦ F (r, y)) s = _ at hcomp
  simp only [id_eq] at hcomp
  rw [hzero, ContinuousLinearMap.zero_comp, mfderiv_eq_fderiv] at hcomp
  have hd : deriv (fun r ↦ F (r, y)) s = 0 := by
    rw [← fderiv_apply_one_eq_deriv, hcomp, zero_apply]
  exact (hpos y s hp.1).ne' hd

local instance : Fact (Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) = n + 1) :=
  ⟨by simp [Module.finrank_prod, Nat.add_comm]⟩




theorem exists_levelGraphDiffeomorph
    {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, 0 < deriv (fun r ↦ F (r, y)) s)
    (hleft : ∀ y : N, F (-ε, y) < 0) (hright : ∀ y : N, 0 < F (ε, y)) :
    letI := openLevelSetChartedSpace hF (graphSlab ε) (graphSlab_regular hF hpos) n 0
    ∃ e : N ≃ₘ⟮𝓡 n, 𝓡 n⟯ openLevelSet F (graphSlab ε) 0,
      ∀ p, e.symm p = (openLevelIncl F (graphSlab ε) 0 p).2 := by
  let := openLevelSetChartedSpace hF (graphSlab ε) (graphSlab_regular hF hpos) n 0
  obtain ⟨u, hu, hroot, huniq⟩ := exists_unique_smooth_level_height hF hε hpos hleft hright
  let e : N ≃ openLevelSet F (graphSlab ε) 0 :=
    { toFun := fun y ↦ ⟨⟨(u y, y), ⟨(hroot y).1, mem_univ y⟩⟩, (hroot y).2⟩
      invFun := fun p ↦ p.1.1.2
      left_inv := fun _ ↦ rfl
      right_inv := by
        intro p
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · exact ((huniq p.1.1.2 p.1.1.1 p.1.2.1).mp p.2).symm
        · rfl }
  refine ⟨{ e with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }, fun _ ↦ rfl⟩
  · intro y
    apply (contMDiffAt_into_openLevelSet_iff hF n 0 (graphSlab ε)
      (graphSlab_regular hF hpos) e y).mpr
    exact (hu y).prodMk contMDiffAt_id
  · exact contMDiff_snd.comp
      (contMDiff_openLevelIncl hF (graphSlab ε) (graphSlab_regular hF hpos) n 0)

end Poincare.Manifold
