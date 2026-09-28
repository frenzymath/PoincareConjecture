import PoincareConjecture.Proofs.M09.AdaptedFieldCoordinates

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

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_metric_pairing_of_adapted {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P Q : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) U)
    (hQ : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, Q t⟩ : TangentBundle (𝓡 n) M)) U)
    (HP : ParametricAlongCurveExtensionOn (n := n) U γ P)
    (HQ : ParametricAlongCurveExtensionOn (n := n) U γ Q)
    (s : ℝ) (hs : s ∈ U) (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (heP : ∀ w : TangentSpace (𝓡 n) (γ s),
      (F.metric (T - s ^ 2)).inner (γ s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P U HP s) w =
        -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) w)
    (heQ : ∀ w : TangentSpace (𝓡 n) (γ s),
      (F.metric (T - s ^ 2)).inner (γ s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ Q U HQ s) w =
        -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (Q s) w) :
    HasDerivAt (fun t ↦ (F.metric (T - t ^ 2)).inner (γ t) (P t) (Q t)) 0 s := by
  let p := γ s
  let e := chartAt E p
  let V := U ∩ γ ⁻¹' e.source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU e.open_source
  have hsV : s ∈ V := ⟨hs, mem_chart_source E p⟩
  have hq : ∀ t ∈ V, γ t ∈ e.source := fun t ht ↦ ht.2
  let y : ℝ → E := fun t ↦ e (γ t)
  let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (P t)
  let w : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (Q t)
  have hv := field_chart_coordinates_smooth p γ P V (hP.mono Set.inter_subset_left) hq
  have hw := field_chart_coordinates_smooth p γ Q V (hQ.mono Set.inter_subset_left) hq
  have hvrep : ∀ t ∈ V, chartVectorField p (v t) (γ t) = P t :=
    fun t ht ↦ chartVectorField_differential p (γ t) (P t) ht.2
  have hwrep : ∀ t ∈ V, chartVectorField p (w t) (γ t) = Q t :=
    fun t ht ↦ chartVectorField_differential p (γ t) (Q t) ht.2
  have hvd := hasDerivAt_coordinates_of_adapted_equation F T b hb hwindow p γ P U V HP
    hV (hγ.mono Set.inter_subset_left) hq v hv (fun t ht ↦ hvrep t ht.2)
    s hs hsV (hU.uniqueDiffOn s hs) htime heP
  have hwd := hasDerivAt_coordinates_of_adapted_equation F T b hb hwindow p γ Q U V HQ
    hV (hγ.mono Set.inter_subset_left) hq w hw (fun t ht ↦ hwrep t ht.2)
    s hs hsV (hU.uniqueDiffOn s hs) htime heQ
  have hy : ContDiffOn ℝ ∞ y V :=
    (contMDiffOn_chart.comp (hγ.mono Set.inter_subset_left) hq).contDiffOn
  have hyd : HasDerivAt y (deriv y s) s :=
    ((hy.contDiffAt (hV.mem_nhds hsV)).differentiableAt (by simp)).hasDerivAt
  have hG : DifferentiableAt ℝ (squareChartMetric F T p) (s, y s) :=
    ((squareChartMetric_smooth F T b hb hwindow p).contDiffAt
      ((isOpen_Ioo.prod e.open_target).mem_nhds ⟨htime, e.map_source hsV.2⟩)).differentiableAt (by simp)
  have hd := hasDerivAt_coordinateTransport_pairing (squareChartMetric F T p) y v w s (deriv y s)
    hG (Filter.Eventually.of_forall (fun z a c ↦ squareChartMetric_symm F T p z a c))
    (fun a ha ↦ squareChartMetric_pos F T p (s, y s) (e.map_source hsV.2) a ha)
    hyd hvd hwd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hsV] with t ht
  have hv' := chartVectorField_at_inverse p (v t) (y t) (e.map_source ht.2)
  have hw' := chartVectorField_at_inverse p (w t) (y t) (e.map_source ht.2)
  dsimp only [y] at hv' hw'
  rw [e.left_inv ht.2, hvrep t ht] at hv'
  rw [e.left_inv ht.2, hwrep t ht] at hw'
  change (F.metric (T - t ^ 2)).inner (γ t) (P t) (Q t) =
    (F.metric (T - t ^ 2)).inner (e.symm (e (γ t))) _ _
  rw [e.left_inv ht.2]
  let a : E := mfderiv (𝓡 n) (𝓡 n) e.symm (e (γ t)) (v t)
  let b : E := mfderiv (𝓡 n) (𝓡 n) e.symm (e (γ t)) (w t)
  have hva : (P t : E) = a := hv'
  have hwb : (Q t : E) = b := hw'
  exact congrArg₂ (fun a b : E ↦ (F.metric (T - t ^ 2)).inner (γ t) a b) hva hwb

end PoincareConjecture.Proofs.M09
