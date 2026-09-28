import PoincareConjecture.Proofs.M09.AdaptedFieldOn
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem IsAdaptedFieldOn.hasDerivAt_pairing {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P Q : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    (s : ℝ) (hs : s ∈ U) (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    HasDerivAt (fun t ↦ (F.metric (T - t ^ 2)).inner (γ t) (P t) (Q t)) 0 s := by
  let p := γ s
  let e := chartAt E p
  let V := U ∩ γ ⁻¹' e.source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU e.open_source
  have hsV : s ∈ V := ⟨hs, mem_chart_source E p⟩
  let y : ℝ → E := fun t ↦ e (γ t)
  let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (P t)
  let w : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (Q t)
  have hy : ContDiffOn ℝ ∞ y V :=
    (contMDiffOn_chart.comp (hγ.mono Set.inter_subset_left) (fun _ ht ↦ ht.2)).contDiffOn
  have hyd : HasDerivAt y (deriv y s) s :=
    ((hy.contDiffAt (hV.mem_nhds hsV)).differentiableAt (by simp)).hasDerivAt
  have hG : DifferentiableAt ℝ (squareChartMetric F T p) (s, y s) :=
    ((squareChartMetric_smooth F T b hb hwindow p).contDiffAt
      ((isOpen_Ioo.prod e.open_target).mem_nhds ⟨htime, e.map_source hsV.2⟩)).differentiableAt
      (by simp)
  have hd := hasDerivAt_coordinateTransport_pairing (squareChartMetric F T p) y v w s
    (deriv y s) hG
    (Filter.Eventually.of_forall (fun z a c ↦ squareChartMetric_symm F T p z a c))
    (fun a ha ↦ squareChartMetric_pos F T p (s, y s) (e.map_source hsV.2) a ha)
    hyd (hP.equation s hs p hsV.2) (hQ.equation s hs p hsV.2)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hsV] with t ht
  have hv' := chartVectorField_at_inverse p (v t) (y t) (e.map_source ht.2)
  have hw' := chartVectorField_at_inverse p (w t) (y t) (e.map_source ht.2)
  dsimp only [y] at hv' hw'
  rw [e.left_inv ht.2, chartVectorField_differential p (γ t) (P t) ht.2] at hv'
  rw [e.left_inv ht.2, chartVectorField_differential p (γ t) (Q t) ht.2] at hw'
  change (F.metric (T - t ^ 2)).inner (γ t) (P t) (Q t) =
    (F.metric (T - t ^ 2)).inner (e.symm (e (γ t))) _ _
  rw [e.left_inv ht.2]
  let a : E := mfderiv (𝓡 n) (𝓡 n) e.symm (e (γ t)) (v t)
  let b : E := mfderiv (𝓡 n) (𝓡 n) e.symm (e (γ t)) (w t)
  have hva : (P t : E) = a := hv'
  have hwb : (Q t : E) = b := hw'
  exact congrArg₂ (fun a b : E ↦ (F.metric (T - t ^ 2)).inner (γ t) a b) hva hwb

theorem IsAdaptedFieldOn.pairing_eq {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P Q : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U : Set ℝ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    (s t : ℝ) (hs : s ∈ U) (ht : t ∈ U) :
    (F.metric (T - s ^ 2)).inner (γ s) (P s) (Q s) =
      (F.metric (T - t ^ 2)).inner (γ t) (P t) (Q t) := by
  have hd := fun r hr ↦ IsAdaptedFieldOn.hasDerivAt_pairing F T b hb hwindow γ P Q U
    hU hγ hP hQ r hr (htime hr)
  exact hU.is_const_of_deriv_eq_zero hconn
    (fun r hr ↦ (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hd r hr).deriv) hs ht

end PoincareConjecture.Proofs.M09
