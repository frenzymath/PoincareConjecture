import PoincareConjecture.Proofs.M09.LocalRegularizedEquation
import PoincareConjecture.Proofs.M09.GeometricUniqueness
import PoincareConjecture.Proofs.M09.WithinODEUniqueness








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem regularizedCurve_phase_eventuallyEqWithin {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (γ δ : ℝ → M)
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hK : UniqueDiffOn ℝ K) (hconn : Set.OrdConnected K)
    (htime : K ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hδ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ δ U)
    (Eγ : ParametricAlongCurveExtensionOn (n := n) K γ (curveVelocityWithin (n := n) γ K))
    (Eδ : ParametricAlongCurveExtensionOn (n := n) K δ (curveVelocityWithin (n := n) δ K))
    (heγ : ∀ s ∈ K, regularizedLGeodesicEquation F T γ K Eγ s)
    (heδ : ∀ s ∈ K, regularizedLGeodesicEquation F T δ K Eδ s)
    (s0 : ℝ) (hs0 : s0 ∈ K)
    (hphase : curvePhase (n := n) γ s0 = curvePhase (n := n) δ s0) :
    curvePhase (n := n) γ =ᶠ[𝓝[K] s0] curvePhase (n := n) δ := by
  let p := γ s0
  let e := chartAt V p
  have hbase : γ s0 = δ s0 := congrArg Bundle.TotalSpace.proj hphase
  have hvel : (curveVelocity γ s0 : V) = (curveVelocity δ s0 : V) :=
    congrArg (fun z : TangentBundle (𝓡 n) M ↦ (z.2 : V)) hphase
  let W := (U ∩ γ ⁻¹' e.source) ∩ (U ∩ δ ⁻¹' e.source)
  have hW : IsOpen W := (hγ.continuousOn.isOpen_inter_preimage hU e.open_source).inter
    (hδ.continuousOn.isOpen_inter_preimage hU e.open_source)
  have hsW : s0 ∈ W := by
    refine ⟨⟨hKU hs0, mem_chart_source V p⟩, hKU hs0, ?_⟩
    change δ s0 ∈ e.source
    rw [← hbase]
    exact mem_chart_source V p
  have hWU : W ⊆ U := fun _ ht ↦ ht.1.1
  have hγd : ∀ t ∈ U, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ t :=
    fun t ht ↦ (hγ.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp)
  have hδd : ∀ t ∈ U, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) δ t :=
    fun t ht ↦ (hδ.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp)
  let a : ℝ → V := fun t ↦ e (γ t)
  let c : ℝ → V := fun t ↦ e (δ t)
  let f : ℝ → V × V := fun t ↦ (a t, deriv a t)
  let g : ℝ → V × V := fun t ↦ (c t, deriv c t)
  have ha : ContDiffOn ℝ ∞ a W :=
    (contMDiffOn_chart.comp (hγ.mono hWU) (fun _ ht ↦ ht.1.2)).contDiffOn
  have hc : ContDiffOn ℝ ∞ c W :=
    (contMDiffOn_chart.comp (hδ.mono hWU) (fun _ ht ↦ ht.2.2)).contDiffOn
  have hfsmooth : ContDiffOn ℝ ∞ f W := ha.prodMk (ha.deriv_of_isOpen hW (by simp))
  have hgsmooth : ContDiffOn ℝ ∞ g W := hc.prodMk (hc.deriv_of_isOpen hW (by simp))
  let S : Set (ℝ × (V × V)) :=
    {z | z.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b) ∧ z.2.1 ∈ e.target}
  let field := regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
  have hS : IsOpen S := (isOpen_Ioo.prod e.open_target).preimage
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hfield : ContDiffOn ℝ 1 field S :=
    (regularizedCoordinatePhase_smooth _ _
      (Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ e.target)
      (isOpen_Ioo.prod e.open_target)
      (squareChartMetric_smooth F T b hb hwindow p)
      (squareChartScalar_smooth F hM04 T b hb hwindow p)
      (fun z hz v hv ↦ squareChartMetric_pos F T p z hz.2 v hv)).of_le (by simp)
  have hf : ∀ᶠ t in 𝓝[K] s0, (t, f t) ∈ S ∧ HasDerivAt f (field (t, f t)) t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hsW)] with t htK htW
    refine ⟨⟨htime htK, e.map_source htW.1.2⟩, ?_⟩
    exact (regularizedEquation_iff_chart_hasDerivAt F hM04 T b hb hwindow p γ U K
      hU hKU hK hγ Eγ t htK (htime htK) htW.1.2).mp (heγ t htK)
  have hg : ∀ᶠ t in 𝓝[K] s0, (t, g t) ∈ S ∧ HasDerivAt g (field (t, g t)) t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hsW)] with t htK htW
    refine ⟨⟨htime htK, e.map_source htW.2.2⟩, ?_⟩
    exact (regularizedEquation_iff_chart_hasDerivAt F hM04 T b hb hwindow p δ U K
      hU hKU hK hδ Eδ t htK (htime htK) htW.2.2).mp (heδ t htK)
  have h0 : f s0 = g s0 := by
    apply Prod.ext
    · exact congrArg e hbase
    · change deriv a s0 = deriv c s0
      rw [(hasDerivAt_chart_curve p γ s0 hsW.1.2 (hγd s0 (hKU hs0))).deriv,
        (hasDerivAt_chart_curve p δ s0 hsW.2.2 (hδd s0 (hKU hs0))).deriv]
      exact congrArg₂ (fun (q : M) (v : V) ↦ (mfderiv (𝓡 n) (𝓡 n) e q) v) hbase hvel
  have hfg := openODE_eventuallyEqWithin S hS field hfield K hconn f g s0 hs0
    ⟨htime hs0, e.map_source hsW.1.2⟩ h0
    (hfsmooth.continuousOn.continuousAt (hW.mem_nhds hsW)).continuousWithinAt
    (hgsmooth.continuousOn.continuousAt (hW.mem_nhds hsW)).continuousWithinAt hf hg
  filter_upwards [hfg, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hsW)] with t ht htW
  have hx : γ t = δ t := e.injOn htW.1.2 htW.2.2 (congrArg Prod.fst ht)
  have hva := chartVectorField_coordinate_velocity p γ t (deriv a t) htW.1.2
    (hγd t (hWU htW)) ((ha.contDiffAt (hW.mem_nhds htW)).differentiableAt (by simp)).hasDerivAt
  have hvc := chartVectorField_coordinate_velocity p δ t (deriv c t) htW.2.2
    (hδd t (hWU htW)) ((hc.contDiffAt (hW.mem_nhds htW)).differentiableAt (by simp)).hasDerivAt
  have hv : (curveVelocity γ t : V) = (curveVelocity δ t : V) :=
    hva.symm.trans ((congrArg₂ (fun (q : M) (v : V) ↦ (chartVectorField p v q : V))
      hx (congrArg Prod.snd ht)).trans hvc)
  exact Bundle.TotalSpace.ext hx (heq_of_eq hv)

theorem regularizedCurve_phase_eqOn_preconnected {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ δ : ℝ → M) (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U)
    (hK : UniqueDiffOn ℝ K) (hconn : IsPreconnected K)
    (htime : K ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hδ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ δ U)
    (Eγ : ParametricAlongCurveExtensionOn (n := n) K γ (curveVelocityWithin (n := n) γ K))
    (Eδ : ParametricAlongCurveExtensionOn (n := n) K δ (curveVelocityWithin (n := n) δ K))
    (heγ : ∀ s ∈ K, regularizedLGeodesicEquation F T γ K Eγ s)
    (heδ : ∀ s ∈ K, regularizedLGeodesicEquation F T δ K Eδ s)
    (s0 : ℝ) (hs0 : s0 ∈ K)
    (hphase : curvePhase (n := n) γ s0 = curvePhase (n := n) δ s0) :
    Set.EqOn (curvePhase (n := n) γ) (curvePhase (n := n) δ) K := by
  let : T2Space (TangentBundle (𝓡 n) M) := tangentBundle_t2Space
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hconn
  let A : Set K := {s | curvePhase (n := n) γ s = curvePhase (n := n) δ s}
  have hclosed : IsClosed A := isClosed_eq
    ((curvePhase_contMDiffOn γ U hU hγ).continuousOn.mono hKU).domRestrict
    ((curvePhase_contMDiffOn δ U hU hδ).continuousOn.mono hKU).domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal := regularizedCurve_phase_eventuallyEqWithin F hM04 T b hb hwindow
      γ δ U K hU hKU hK hconn.ordConnected htime hγ hδ Eγ Eδ heγ heδ t t.property ht
    exact (eventually_nhds_subtype_iff K t
      (fun r ↦ curvePhase (n := n) γ r = curvePhase (n := n) δ r)).mpr hlocal
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨s0, hs0⟩, hphase⟩
  intro t ht
  have hm : (⟨t, ht⟩ : K) ∈ A := by rw [hAll]; trivial
  exact hm

end PoincareConjecture.Proofs.M09
