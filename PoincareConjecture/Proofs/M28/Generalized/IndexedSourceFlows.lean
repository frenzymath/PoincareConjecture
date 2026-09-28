import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFamilyScales
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckHalfFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceMetricSpace

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E) (v : ℕ → ℝ)
  (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper)

def selectedOriginalNeck (k : ℕ) :
    GeneralizedStrongNeck (E (k + H.shift)).flow (E (k + H.shift)).time epsilon :=
  (H.segment k).neckAt (v k) (hv k)

abbrev selectedSourceOpen (k : ℕ) :
    TopologicalSpace.Opens ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier :=
  strongNeckOpen (H.selectedOriginalNeck v hv k)

noncomputable def rawSourceRescaling (k : ℕ) :
    RescaledRawCylinderData (U := H.selectedSourceOpen v hv k)
      (J := strongNeckBackwardInterval)
      (strongNeckCylinder (H.selectedOriginalNeck v hv k))
      (GeneralizedStrongNeck.physical_interval_subset (H.selectedOriginalNeck v hv k)) :=
  Classical.choice (GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow
    (H.selectedOriginalNeck v hv k))

noncomputable def normalizedSourceFlow (k : ℕ) :
    RicciFlow 3 (H.selectedSourceOpen v hv k) (Icc (-(1 / 2 : ℝ)) 0) :=
  GeneralizedStrongNeck.rescaled_half_flow
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

noncomputable def normalizedSourceNeck (k : ℕ) :
    EpsilonNeck ((H.normalizedSourceFlow v hv k).metric 0) :=
  GeneralizedStrongNeck.rescaled_half_source_neck
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)
      (H.segment k).epsilon_lt_half

@[instance_reducible] noncomputable def normalizedSourceMetricSpace (k : ℕ) :
    MetricSpace (H.selectedSourceOpen v hv k) :=
  GeneralizedStrongNeck.rescaled_source_metricSpace
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

theorem normalizedSourceNeck_center_val (k : ℕ) :
    ((H.normalizedSourceNeck v hv k).center :
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier) =
      (H.segment k).path (v k) :=
  (H.segment k).neckAt_center (v k) (hv k)

theorem normalizedSourceNeck_scalar_one (k : ℕ) :
    ((H.normalizedSourceFlow v hv k).connection 0).scalarCurvature
      (H.normalizedSourceNeck v hv k).center = 1 :=
  GeneralizedStrongNeck.rescaled_half_scalar_at_center
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

theorem normalizedSourceMetricSpace_topology (k : ℕ) :
    let d := H.normalizedSourceMetricSpace v hv k
    (inferInstance : TopologicalSpace (H.selectedSourceOpen v hv k)) =
      d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
  GeneralizedStrongNeck.rescaled_source_metricSpace_topology
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

theorem normalizedSourceMetricSpace_edist (k : ℕ)
    (x y : H.selectedSourceOpen v hv k) :
    letI := H.normalizedSourceMetricSpace v hv k
    edist x y = ((H.normalizedSourceFlow v hv k).metric 0).edist x y :=
  GeneralizedStrongNeck.rescaled_source_metricSpace_edist
    (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k) x y

theorem normalizedSource_original_scalar_tendsto_atTop :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.normalizedSourceNeck v hv k).center.val⟩)
      atTop atTop :=
  H.neck_center_scalar_tendsto_atTop v hv

end PoincareConjecture.M28.CounterexampleNeckFamily
