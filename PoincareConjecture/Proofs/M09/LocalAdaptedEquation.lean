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

def LocalAdaptedEquation {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t)) (s : ℝ) : Prop :=
  ∀ p : M, γ s ∈ (chartAt E p).source →
    let y : ℝ → E := fun t ↦ (chartAt E p) (γ t)
    let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ t) (P t)
    HasDerivAt v (coordinateTransportOperator (squareChartMetric F T p)
      (s, y s) (deriv y s) (v s)) s

theorem localAdaptedEquation_of_pullback {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t))
    (K U : Set ℝ) (H : ParametricAlongCurveExtensionOn (n := n) K γ P)
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) U)
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) (hKd : UniqueDiffWithinAt ℝ K s)
    (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (heq : ∀ w : TangentSpace (𝓡 n) (γ s),
      (F.metric (T - s ^ 2)).inner (γ s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K H s) w =
        -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) w) :
    LocalAdaptedEquation F T γ P s := by
  intro p hp
  let V := U ∩ γ ⁻¹' (chartAt E p).source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E p).open_source
  have hq : ∀ t ∈ V, γ t ∈ (chartAt E p).source := fun _ ht ↦ ht.2
  let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ t) (P t)
  have hv := field_chart_coordinates_smooth p γ P V (hP.mono Set.inter_subset_left) hq
  exact hasDerivAt_coordinates_of_adapted_equation F T b hb hwindow p γ P K V H
    hV (hγ.mono Set.inter_subset_left) hq v hv
    (fun t ht ↦ chartVectorField_differential p (γ t) (P t) ht.2.2)
    s hs ⟨hsU, hp⟩ hKd htime heq

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem pullback_adapted_of_localAdaptedEquation {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t))
    (K U : Set ℝ) (H : ParametricAlongCurveExtensionOn (n := n) K γ P)
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) U)
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) (hKd : UniqueDiffWithinAt ℝ K s)
    (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (heq : LocalAdaptedEquation F T γ P s) (w : TangentSpace (𝓡 n) (γ s)) :
    (F.metric (T - s ^ 2)).inner (γ s)
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K H s) w =
      -(2 * s) * (F.connection (T - s ^ 2)).ricci (γ s) (P s) w := by
  let p := γ s
  let e := chartAt E p
  let V := U ∩ γ ⁻¹' e.source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU e.open_source
  have hsV : s ∈ V := ⟨hsU, mem_chart_source E p⟩
  have hq : ∀ t ∈ V, γ t ∈ e.source := fun _ ht ↦ ht.2
  let y : ℝ → E := fun t ↦ e (γ t)
  let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (P t)
  have hv := field_chart_coordinates_smooth p γ P V (hP.mono Set.inter_subset_left) hq
  have hvrep : ∀ t ∈ V, chartVectorField p (v t) (γ t) = P t :=
    fun t ht ↦ chartVectorField_differential p (γ t) (P t) ht.2
  have hpull := pullbackCovariantDerivative_eq_chart F T b hb hwindow p γ P K V H
    hV (hγ.mono Set.inter_subset_left) hq v hv (fun t ht ↦ hvrep t ht.2)
    s hs hsV hKd htime
  have hd : deriv v s = coordinateTransportOperator (squareChartMetric F T p)
      (s, y s) (deriv y s) (v s) := (heq p hsV.2).deriv
  rw [hd] at hpull
  let wc : E := mfderiv (𝓡 n) (𝓡 n) e (γ s) w
  have hw : chartVectorField p wc (γ s) = w :=
    chartVectorField_differential p (γ s) w hsV.2
  have hpair := squareChartTransport_pairing F T b hb hwindow p s htime
    (y s) (e.map_source hsV.2) (deriv y s) (v s) wc
  have hconn := squareChartConnection_eq F T b hb hwindow p s htime
    (y s) (e.map_source hsV.2) (deriv y s) (v s)
  dsimp only [y] at hpair hconn
  rw [e.left_inv hsV.2] at hpair hconn
  rw [← hconn, hw, hvrep s hsV] at hpair
  rw [hpull]
  change (F.metric (T - s ^ 2)).inner (γ s)
    ((mfderiv (𝓡 n) (𝓡 n) e (γ s)).inverse (_ + _)) w = _
  rw [map_add]
  exact hpair

theorem LocalAdaptedEquation.congr {J : Set ℝ} {F : RicciFlow n M J} {T s : ℝ}
    {γ : ℝ → M} {P Q : ∀ t, TangentSpace (𝓡 n) (γ t)}
    (h : LocalAdaptedEquation F T γ P s) (heq : ∀ᶠ t in 𝓝 s, P t = Q t) :
    LocalAdaptedEquation F T γ Q s := by
  intro p hp
  have hv : (fun t ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ t) (P t)) =ᶠ[𝓝 s]
      (fun t ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ t) (Q t)) := by
    filter_upwards [heq] with t ht
    rw [ht]
  have hd := (h p hp).congr_of_eventuallyEq hv.symm
  simpa only [hv.eq_of_nhds] using hd

end PoincareConjecture.Proofs.M09
