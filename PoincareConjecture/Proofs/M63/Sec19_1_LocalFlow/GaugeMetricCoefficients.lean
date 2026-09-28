import PoincareConjecture.Proofs.M63.Mathlib.PartialFDeriv
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.M09.InverseChartVector

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem RiemannianMetric.IsSmoothFamilyOn.contDiffWithinAt_spacetime_pullbackCoefficients_m63
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {f : E → M} {y : E} (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f y)
    {t : ℝ} (ht : t ∈ J) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × E => (g p.1).pullbackCoefficients f p.2) (J ×ˢ univ) (t, y) := by
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg hf ht
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [RiemannianMetric.constant_chart_bilinear_coordinates
    (n := n) (M := E) (fun _ _ => rfl)] at hc
  have hid : ContMDiffAt 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × E => (p.1, p.2)) (t, y) :=
    contDiffAt_fst.contMDiffAt.prodMk contDiffAt_snd.contMDiffAt
  convert! (hc.comp (t, y) hid.contMDiffWithinAt (fun _ hp => hp)).contDiffWithinAt using 1

namespace M63

variable {a b : ℝ}

theorem chart_metric_coefficients_contDiffOn (F : RicciFlow n M (Icc a b)) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => (F.metric z.1).pullbackCoefficients (chartAt E p).symm z.2)
      (Icc a b ×ˢ (chartAt E p).target) := by
  intro z hz
  exact (F.smooth.contDiffWithinAt_spacetime_pullbackCoefficients_m63
    (contMDiffOn_chart_symm.contMDiffAt ((chartAt E p).open_target.mem_nhds hz.2))
    hz.1).mono (fun _ hw => ⟨hw.1, mem_univ _⟩)

theorem chart_metric_spatial_derivative_contDiffOn
    (F : RicciFlow n M (Icc a b)) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => fderiv ℝ
        ((F.metric z.1).pullbackCoefficients (chartAt E p).symm) z.2)
      (Icc a b ×ˢ (chartAt E p).target) :=
  (chart_metric_coefficients_contDiffOn F p).fderiv_snd_of_isOpen_m63
    (m := ∞) (chartAt E p).open_target (by simp)

theorem chart_metric_pairing_pos (F : RicciFlow n M (Icc a b)) (p : M)
    (t : ℝ) {y V : E} (hy : y ∈ (chartAt E p).target) (hV : V ≠ 0) :
    0 < (F.metric t).pullbackCoefficients (chartAt E p).symm y V V := by
  have hinj := (Proofs.M09.inverseChartDifferential_bijective p y hy).1
  have hne : mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y V ≠ 0 := by
    intro hzero
    exact hV (hinj (by simpa only [map_zero] using hzero))
  exact (F.metric t).pos ((chartAt E p).symm y) _ hne

end M63
end PoincareConjecture
