import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Pullback
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem exists_smooth_localFlow
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X)) (x : M) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ x ∈ V ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      ∀ y ∈ V, IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y)) X (Ioo (-δ) δ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) x
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ∞))
  have hc (y : M) (hy : y ∈ c.source) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c y :=
    hchart.contMDiffAt (extChartAt_source_mem_nhds' hy)
  have hci (z : E) (hz : z ∈ c.target) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  let F : E → E := fun z => mfderiv (𝓡 n) (𝓡 n) c (c.symm z) (X (c.symm z))
  have hF : ContDiffOn ℝ ∞ F c.target := by
    intro z hz
    have hd := ((hc _ (c.map_target hz)).mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates
      (hX _) (hc _ (c.map_target hz))
    have hs := (contMDiff_snd_tangentBundle_modelSpace E (𝓡 n)).contMDiffAt.comp _ hd
    exact (contMDiffAt_iff_contDiffAt.mp (hs.comp z (hci z hz))).contDiffWithinAt
  have hpush (z : E) (hz : z ∈ c.target) :
      mfderiv (𝓡 n) (𝓡 n) c.symm z (F z) = X (c.symm z) := by
    have h := congrArg (fun L => L (X (c.symm z)))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n)
        (c.map_target hz))
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
      ContinuousLinearMap.comp_apply] at h
    change mfderiv (𝓡 n) (𝓡 n) c.symm (c (c.symm z)) (F z) = X (c.symm z) at h
    have hz' : c (c.symm z) = z := c.right_inv hz
    rw [hz'] at h
    exact h
  obtain ⟨B, δ, q, hB, hxB, hBc, hδ, hq, hq0, hqmem, hqtime⟩ :=
    Poincare.ODE.LocalFlow.exists_smooth_localFlow (isOpen_extChartAt_target x) hF
      (mem_extChartAt_target x)
  let V := c.source ∩ c ⁻¹' B
  have hV : IsOpen V :=
    hchart.continuousOn.isOpen_inter_preimage (isOpen_extChartAt_source x) hB
  let Φ : ℝ × M → M := fun p => c.symm (q (c p.2, p.1))
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo (-δ) δ ×ˢ V) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (fun p : ℝ × M => (c p.2, p.1)) (t, y) :=
      ((hc y hy.1).comp (t, y) contMDiffAt_snd).prodMk contMDiffAt_fst
    have hqm : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞ q (c y, t) := by
      have hqd := hq.contDiffAt ((hB.prod isOpen_Ioo).mem_nhds
        (show (c y, t) ∈ B ×ˢ Ioo (-δ) δ from ⟨hy.2, ht⟩))
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hqd.contMDiffAt
    exact ((hci _ (hqmem _ hy.2 t ht)).comp (t, y) (hqm.comp (t, y) hp)).contMDiffWithinAt
  refine ⟨V, δ, Φ, hV, ⟨mem_extChartAt_source x, hxB⟩, hδ, hΦ, ?_, ?_⟩
  · intro y hy
    change c.symm (q (c y, 0)) = y
    rw [hq0 _ hy.2, c.left_inv hy.1]
  · intro y hy t ht
    have hd := ((hci _ (hqmem _ hy.2 t ht)).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (hqtime _ hy.2 t ht).hasFDerivAt.hasMFDerivAt
    apply HasMFDerivAt.hasMFDerivWithinAt
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change mfderiv (𝓡 n) (𝓡 n) c.symm (q (c y, t)) (a • F (q (c y, t))) =
      a • X (c.symm (q (c y, t)))
    rw [map_smul, hpush _ (hqmem _ hy.2 t ht)]

end Poincare.Manifold
