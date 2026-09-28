import PoincareConjecture.Proofs.M09.LocalLinearTransport
import PoincareConjecture.Proofs.M09.SquareChartTransport
import PoincareConjecture.Proofs.M09.ChartFieldDerivative
import PoincareConjecture.Proofs.M09.CompactFieldExtension

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_local_adapted_field {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U) (s0 : ℝ) (hs0 : s0 ∈ U) :
    ∃ (W : Set ℝ) (d : ℝ), IsOpen W ∧ s0 ∈ W ∧ W ⊆ U ∧ 0 < d ∧
      ∀ t0 ∈ W, ∀ v0 : TangentSpace (𝓡 n) (γ t0),
        let I := Set.Ioo (t0 - d) (t0 + d)
        ∃ P : ∀ t, TangentSpace (𝓡 n) (γ t),
          I ⊆ U ∧ P t0 = v0 ∧
          ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
            (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) I ∧
          ∃ H : ParametricAlongCurveExtensionOn (n := n) I γ P,
            ∀ t ∈ I, ∀ w : TangentSpace (𝓡 n) (γ t),
              (F.metric (T - t ^ 2)).inner (γ t)
                (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P I H t) w =
                -(2 * t) * (F.connection (T - t ^ 2)).ricci (γ t) (P t) w := by
  let p := γ s0
  let e := chartAt E p
  let D := U ∩ γ ⁻¹' e.source
  have hD : IsOpen D := hγ.continuousOn.isOpen_inter_preimage hU e.open_source
  have hsD : s0 ∈ D := ⟨hs0, mem_chart_source E p⟩
  let y : ℝ → E := fun t ↦ e (γ t)
  have hy : ContDiffOn ℝ ∞ y D :=
    (contMDiffOn_chart.comp (hγ.mono Set.inter_subset_left) (fun t ht ↦ ht.2)).contDiffOn
  have hdy : ContDiffOn ℝ ∞ (deriv y) D := hy.deriv_of_isOpen hD (by simp)
  let S := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ e.target
  have hS : IsOpen S := isOpen_Ioo.prod e.open_target
  have hL := coordinateTransportOperator_contDiffOn (squareChartMetric F T p) S hS
    (squareChartMetric_smooth F T b hb hwindow p)
    (fun z hz v hv ↦ squareChartMetric_pos F T p z hz.2 v hv)
  let A : ℝ → E →L[ℝ] E := fun t ↦
    coordinateTransportOperator (squareChartMetric F T p) (t, y t) (deriv y t)
  have hparam : ContDiffOn ℝ ∞ (fun t : ℝ ↦ ((t, y t), deriv y t)) D :=
    (contDiffOn_id.prodMk hy).prodMk hdy
  have hA := hL.comp (f := fun t : ℝ ↦ ((t, y t), deriv y t)) hparam
    (fun t ht ↦ ⟨⟨htime ht.1, e.map_source ht.2⟩, Set.mem_univ _⟩)
  obtain ⟨W, d, hW, hsW, hWD, hd, hsolve⟩ :=
    exists_uniform_local_linear_solution D hD A hA s0 hsD
  refine ⟨W, d, hW, hsW, hWD.trans Set.inter_subset_left, hd, ?_⟩
  intro t0 ht0 v0
  let I := Set.Ioo (t0 - d) (t0 + d)
  let vinit : E := mfderiv (𝓡 n) (𝓡 n) e (γ t0) v0
  obtain ⟨v, hID, hv0, hv, hode⟩ := hsolve t0 ht0 vinit
  let P : ∀ t, TangentSpace (𝓡 n) (γ t) := fun t ↦ chartVectorField p (v t) (γ t)
  have hIU : I ⊆ U := hID.trans Set.inter_subset_left
  have hq : ∀ t ∈ I, γ t ∈ e.source := fun t ht ↦ (hID ht).2
  have hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) I :=
    (chartVectorField_param_smooth p v I hv).comp
      (contMDiffOn_id.prodMk (hγ.mono hIU)) (fun t ht ↦ ⟨ht, hq t ht⟩)
  let H : ParametricAlongCurveExtensionOn (n := n) I γ P :=
    chartFieldExtensionAlong p γ P v I I isOpen_Ioo (Set.Subset.refl I) hv hq
      (fun _ _ ↦ rfl)
  refine ⟨P, hIU, ?_, hP, H, ?_⟩
  · change chartVectorField p (v t0) (γ t0) = v0
    rw [hv0]
    exact chartVectorField_differential p (γ t0) v0 (hWD ht0).2
  · intro t ht w
    have hγt : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ t :=
      (hγ.contMDiffAt (hU.mem_nhds (hIU ht))).mdifferentiableAt (by simp)
    have hyt : HasDerivAt y (deriv y t) t :=
      ((hy.contDiffAt (hD.mem_nhds (hID ht))).differentiableAt (by simp)).hasDerivAt
    have hvelocity : curveVelocityWithin (n := n) γ I t =
        chartVectorField p (deriv y t) (γ t) := by
      unfold curveVelocityWithin
      rw [mfderivWithin_eq_mfderiv (isOpen_Ioo.uniqueMDiffWithinAt ht) hγt]
      exact (chartVectorField_coordinate_velocity p γ t (deriv y t) (hq t ht) hγt hyt).symm
    have hpull := chartFieldExtensionAlong_pullback F (fun r ↦ T - r ^ 2) p γ P v I I
      isOpen_Ioo (Set.Subset.refl I) hv hq (fun _ _ ↦ rfl) t (A t (v t)) (hode t ht)
    change pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P I H t = _ at hpull
    rw [hvelocity] at hpull
    let wc : E := mfderiv (𝓡 n) (𝓡 n) e (γ t) w
    have hw : chartVectorField p wc (γ t) = w :=
      chartVectorField_differential p (γ t) w (hq t ht)
    have hpair := squareChartTransport_pairing F T b hb hwindow p t (htime (hIU ht))
      (y t) (e.map_source (hq t ht)) (deriv y t) (v t) wc
    dsimp only at hpair
    change (F.metric (T - t ^ 2)).inner (e.symm (e (γ t))) _ _ = _ at hpair
    rw [e.left_inv (hq t ht), hw] at hpair
    rw [hpull]
    exact hpair

end PoincareConjecture.Proofs.M09
