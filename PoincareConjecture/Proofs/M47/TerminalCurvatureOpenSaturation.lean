import PoincareConjecture.Proofs.M47.TerminalCurvatureFlowDifferential
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

theorem terminalCurvature_sphere_saturation_open
    {M A : Type*} [TopologicalSpace M] [TopologicalSpace A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) A]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 2) ∞ A]
    (V : (x : M) → TangentSpace (𝓡 3) x) (Phi : ℝ → M → M)
    (hzero : ∀ x, Phi 0 x = x)
    (hPhi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun tx : ℝ × M => Phi tx.1 tx.2))
    (hcurve : ∀ x, IsMIntegralCurve (fun t => Phi t x) V)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    (F : A → M) (hF : ContMDiff (𝓡 2) (𝓡 3) ∞ F)
    (htransverse : ∀ z,
      Function.Injective (mfderiv (𝓡 2) (𝓡 3) F z) ∧
      V (F z) ∉ range (mfderiv (𝓡 2) (𝓡 3) F z)) :
    IsOpen {x | ∃ t : ℝ, ∃ k ∈ range F, Phi t k = x} := by
  let : ChartedSpace (ℝ × EuclideanSpace ℝ (Fin 2)) (ℝ × A) :=
    prodChartedSpace ℝ ℝ (EuclideanSpace ℝ (Fin 2)) A
  let S : Set M := {x | ∃ t : ℝ, ∃ k ∈ range F, Phi t k = x}
  let Q : ℝ × A → M := fun tz => Phi tz.1 (F tz.2)
  have hQ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ Q :=
    hPhi.comp (contMDiff_fst.prodMk (hF.comp contMDiff_snd))
  have hcentral (z : A) : S ∈ 𝓝 (F z) := by
    have hbij := terminalCurvature_flow_sphere_bijective V Phi hzero hPhi hcurve F hF z
      (htransverse z).1 (htransverse z).2
    have hmap : map Q (𝓝 (0, z)) = 𝓝 (Q (0, z)) := by
      apply Poincare.Geometry.Manifold.map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces
        (E := ℝ × EuclideanSpace ℝ (Fin 2)) (F := EuclideanSpace ℝ (Fin 3))
      · rw [modelWithCornersSelf_prod]
        exact hQ (0, z)
      · rw [modelWithCornersSelf_prod]
        exact hbij
    have hmem : S ∈ map Q (𝓝 (0, z)) := by
      change Q ⁻¹' S ∈ 𝓝 (0, z)
      apply Filter.mem_of_superset Filter.univ_mem
      rintro ⟨t, y⟩ _
      exact ⟨t, F y, mem_range_self y, rfl⟩
    rw [hmap] at hmem
    simpa only [Q, hzero] using hmem
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨t, k, ⟨z, rfl⟩, rfl⟩
  have hinv : Phi (-t) (Phi t (F z)) = F z := by
    rw [← hadd, neg_add_cancel, hzero]
  have hc : ContinuousAt (Phi (-t)) (Phi t (F z)) :=
    (hPhi.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
  have hpre : Phi (-t) ⁻¹' S ∈ 𝓝 (Phi t (F z)) :=
    hc.preimage_mem_nhds (by rw [hinv]; exact hcentral z)
  apply Filter.mem_of_superset hpre
  rintro y ⟨s, k, hk, heq⟩
  refine ⟨t + s, k, hk, ?_⟩
  rw [hadd, heq, ← hadd, add_neg_cancel, hzero]

end PoincareConjecture.M47
