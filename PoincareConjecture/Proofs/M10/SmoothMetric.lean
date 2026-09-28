import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open Bundle ContinuousLinearMap Filter Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

theorem backward_metric_contMDiffAt
    (hwindow : Icc (T - τmax) T ⊆ J)
    (z : M × ℝ) (hz : z ∈ univ ×ˢ Ioo 0 τmax) :
    ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      ((𝓡 n).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun w : M × ℝ ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q →L[ℝ] ℝ)
        w.1 ((F.metric (T - w.2)).inner w.1)) z := by
  have htime : T - z.2 ∈ Ioo (T - τmax) T := by
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hnhds : J ×ˢ (univ : Set M) ∈ 𝓝 (T - z.2, z.1) :=
    Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨htime, mem_univ _⟩)
      (fun _ hw ↦ ⟨hwindow ⟨hw.1.1.le, hw.1.2.le⟩, hw.2⟩)
  have hmetric := F.smooth.contMDiffAt hnhds
  exact hmetric.comp z
    ((contMDiffAt_const.sub contMDiffAt_snd).prodMk contMDiffAt_fst)

noncomputable def backwardMetricCoordinates (F : RicciFlow n M J) (T : ℝ) (q₀ : M)
    (w : M × ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (fun q ↦ TangentSpace (𝓡 n) q →L[ℝ] ℝ)
    q₀ w.1 q₀ w.1 ((F.metric (T - w.2)).inner w.1)

set_option backward.isDefEq.respectTransparency false in

theorem backwardMetricCoordinates_contMDiffAt
    (hwindow : Icc (T - τmax) T ⊆ J)
    (z : M × ℝ) (hz : z ∈ univ ×ˢ Ioo 0 τmax) :
    ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      ∞ (backwardMetricCoordinates F T z.1) z := by
  have h := backward_metric_contMDiffAt (F := F) hwindow z hz
  rw [contMDiffAt_hom_bundle] at h
  exact h.2

set_option backward.isDefEq.respectTransparency false in

theorem backwardMetricCoordinates_apply (q₀ : M) (w : M × ℝ)
    (hw : w.1 ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) q₀).baseSet)
    (v v' : TangentSpace (𝓡 n) w.1) :
    backwardMetricCoordinates F T q₀ w
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) q₀).continuousLinearMapAt ℝ w.1 v)
      ((trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) q₀).continuousLinearMapAt ℝ w.1 v') =
      (F.metric (T - w.2)).inner w.1 v v' := by
  unfold backwardMetricCoordinates
  rw [inCoordinates_apply_eq₂ hw hw (mem_univ _)]
  simp only [Trivialization.continuousLinearMapAt_apply,
    Trivialization.symm_linearMapAt _ hw]
  change (Bundle.Trivial.trivialization M ℝ).linearMapAt ℝ w.1 _ = _
  simp only [Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]

noncomputable def coordinateBackwardMetric (F : RicciFlow n M J) (T : ℝ) (q₀ : M)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  backwardMetricCoordinates F T q₀ ((extChartAt (𝓡 n) q₀).symm z.1, z.2)

set_option backward.isDefEq.respectTransparency false in

theorem coordinateBackwardMetric_contDiffAt
    (hwindow : Icc (T - τmax) T ⊆ J)
    (q₀ : M) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    ContDiffAt ℝ ∞ (coordinateBackwardMetric F T q₀)
      (extChartAt (𝓡 n) q₀ q₀, τ) := by
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) q₀).symm
      (extChartAt (𝓡 n) q₀ q₀) :=
    (contMDiffOn_extChartAt_symm q₀).contMDiffAt
      (extChartAt_target_mem_nhds (I := 𝓡 n) q₀)
  have h := backwardMetricCoordinates_contMDiffAt (F := F) hwindow
    (q₀, τ) ⟨mem_univ _, hτ, hmax⟩
  have hpre : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun w : EuclideanSpace ℝ (Fin n) × ℝ ↦
        ((extChartAt (𝓡 n) q₀).symm w.1, w.2))
      (extChartAt (𝓡 n) q₀ q₀, τ) :=
    (hi.comp (f := fun w : EuclideanSpace ℝ (Fin n) × ℝ ↦ w.1)
      (extChartAt (𝓡 n) q₀ q₀, τ) contMDiffAt_fst).prodMk contMDiffAt_snd
  have h' : ContMDiffAt ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      ∞ (backwardMetricCoordinates F T q₀)
      ((extChartAt (𝓡 n) q₀).symm (extChartAt (𝓡 n) q₀ q₀), τ) := by
    simpa only [extChartAt_to_inv] using h
  have hcomp := h'.comp
    (f := fun w : EuclideanSpace ℝ (Fin n) × ℝ ↦
      ((extChartAt (𝓡 n) q₀).symm w.1, w.2))
    (extChartAt (𝓡 n) q₀ q₀, τ) hpre
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcomp
  exact hcomp.contDiffAt

end PoincareConjecture.M10
