import PoincareConjecture.Proofs.M35.Uniqueness.InitialKilling
import PoincareConjecture.Proofs.M03.MetricGradientEvolution

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

set_option backward.isDefEq.respectTransparency false in

theorem linear_killing_defect_hasDerivAt
    {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 G.lifetime) (x u v : StandardCapSpace) :
    HasDerivAt
      (fun s => DeTurckNative.metricLieDerivative (G.flow.connection s)
        (fun y => B y) x u v)
      (fderiv ℝ (fun y => -2 * (G.flow.connection t).ricci y u v) x (B x) -
        2 * (G.flow.connection t).ricci x (B u) v -
        2 * (G.flow.connection t).ricci x u (B v)) t := by
  have hti : t ∈ interior (Set.Ico 0 G.lifetime) := by
    simpa only [interior_Ico] using ht
  have hfield (w : StandardCapSpace) :
      ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞
        (fun y : StandardCapSpace => Bundle.TotalSpace.mk' StandardCapSpace y
          (E := TangentSpace (𝓡 3)) w) Set.univ := by
    apply ContMDiff.contMDiffOn
    intro y
    rw [Bundle.contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := w)⟩
  have hd := Proofs.M03.hasDerivAt_ricciFlow_metric_spatial_derivative
    G.flow hti isOpen_univ (fun _ => u) (fun _ => v)
    (hfield u) (hfield v) x (y := x) (by simp) (by simp) (B x)
  change HasDerivAt (fun s => fderiv ℝ (fun y => (G.flow.metric s).inner y u v) x (B x))
    (fderiv ℝ (fun y => -2 * (G.flow.connection t).ricci y u v) x (B x)) t at hd
  have hu := (G.flow.equation t (interior_subset hti) x (B u) v).hasDerivAt
    (mem_interior_iff_mem_nhds.mp hti)
  have hv := (G.flow.equation t (interior_subset hti) x u (B v)).hasDerivAt
    (mem_interior_iff_mem_nhds.mp hti)
  convert! (hd.add hu).add hv using 1
  · funext s
    exact metricLieDerivative_linear (G.flow.connection s) B x u v
  · ring

end PoincareConjecture.M35.Uniqueness
