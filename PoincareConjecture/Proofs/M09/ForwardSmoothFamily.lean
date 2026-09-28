import PoincareConjecture.Proofs.M09.SmoothFamilyRestart









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => ℝ × (V × V)

set_option backward.isDefEq.respectTransparency false in
theorem univ_Ico_subset_normalizedSquareFamily_smoothFamilyDomain {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - b) T)) (p0 : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    Set.univ ×ˢ Set.Ico 0 (Real.sqrt b) ⊆ smoothFamilyDomain (n := n)
      (fun z ↦ normalizedSquareFamily F T b p0 z.1 z.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  rintro ⟨Z0, S⟩ ⟨_, hS⟩
  let f : TangentSpace (𝓡 n) p0 × ℝ → M :=
    fun z ↦ normalizedSquareFamily F T b p0 z.1 z.2
  let B := {s : ℝ | (Z0, s) ∈ smoothFamilyDomain (n := n) f}
  have hB : IsOpen B := (isOpen_smoothFamilyDomain (n := n) f).preimage
    (continuous_const.prodMk continuous_id)
  have h0 : (0 : ℝ) ∈ B :=
    normalizedSquareFamily_zero_mem_smoothFamilyDomain F hM04 T b hb hwindow p0 Z0
  have hclosed : closure B ∩ Set.Icc 0 S ⊆ B := by
    rintro t ⟨htcl, htS⟩
    rcases eq_or_lt_of_le htS.1 with heq | htpos
    · simpa only [← heq] using h0
    have htb : t < Real.sqrt b := htS.2.trans_lt hS.2
    let q0 : TangentBundle (𝓡 n) M := ⟨p0, (2 : ℝ) • Z0⟩
    let γ := normalizedSquareFamily F T b p0 Z0
    let D := maximalRegularizedDomain F T b 0 q0
    have hD : IsOpen D := isOpen_maximalRegularizedDomain F T b 0 q0
    have hγ : IsLocalRegularizedCurveOn F T γ D :=
      maximalRegularizedCurve_isLocal F hM04 T b hb hwindow 0 q0
    have htD : t ∈ D :=
      Ico_subset_maximalRegularizedDomain F hM04 T b hb hwindow hcurvature q0 ⟨htS.1, htb⟩
    let p := γ t
    let phase := curvePhase (n := n) γ
    let psi : ℝ → Q := fun r ↦ (r, tangentChartPhase p (phase r))
    have htime : t ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) :=
      ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hb)).trans htpos, htb⟩
    obtain ⟨A⟩ := nonempty_localRegularizedRestartFamily F hM04 T b hb hwindow p (psi t)
      ⟨htime, (chartAt V p).map_source (mem_chart_source V p)⟩
    let C := D ∩ γ ⁻¹' (chartAt V p).source
    have hC : IsOpen C :=
      hγ.smooth.continuousOn.isOpen_inter_preimage hD (chartAt V p).open_source
    have htC : t ∈ C := ⟨htD, mem_chart_source V p⟩
    have hphase : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞ phase C :=
      (curvePhase_contMDiffOn γ D hD hγ.smooth).mono Set.inter_subset_left
    have hcoord : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, V × V)) ∞
        (fun r ↦ tangentChartPhase p (phase r)) C :=
      (tangentChartPhase_contMDiffOn p).comp hphase (fun r hr ↦ hr.2)
    have hpsi : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, Q)) ∞ psi C :=
      (contMDiffOn_prod_module_iff psi).mpr ⟨contMDiffOn_id, hcoord⟩
    let N := (C ∩ psi ⁻¹' A.neighborhood) ∩
      (Set.Ioo (t - A.radius) (t + A.radius) ∩ Set.Ioo 0 (Real.sqrt b))
    have hN : IsOpen N :=
      (hpsi.continuousOn.isOpen_inter_preimage hC A.neighborhood_open).inter
        (isOpen_Ioo.inter isOpen_Ioo)
    have htN : t ∈ N := ⟨⟨htC, A.center_mem⟩,
      ⟨by linarith [A.radius_pos], by linarith [A.radius_pos]⟩, htpos, htb⟩
    obtain ⟨r, hrN, hrB⟩ := mem_closure_iff.mp htcl N hN htN
    have hrt : t ∈ Set.Ioo (r - A.radius) (r + A.radius) := by
      constructor <;> linarith [hrN.2.1.1, hrN.2.1.2]
    exact normalizedSquareFamily_mem_smoothFamilyDomain_of_restart F hM04 T b hb hwindow
      hcurvature p0 p (psi t) A Z0 r t ⟨hrN.2.2.1.le, hrN.2.2.2⟩ htpos hrt
      hrN.1.1.2 hrN.1.2 hrB
  have hsub : Set.Icc 0 S ⊆ B :=
    isPreconnected_Icc.subset_of_closure_inter_subset hB ⟨0, ⟨le_rfl, hS.1⟩, h0⟩ hclosed
  exact hsub ⟨hS.1, le_rfl⟩

end PoincareConjecture.Proofs.M09
