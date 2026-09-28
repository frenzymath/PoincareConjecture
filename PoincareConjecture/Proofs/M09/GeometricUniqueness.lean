import PoincareConjecture.Proofs.M09.CurvePhase
import PoincareConjecture.Proofs.M09.GeometricODE
import PoincareConjecture.Proofs.M09.VelocityRestriction
import PoincareConjecture.Proofs.M09.SquareChartAtFlow
import PoincareConjecture.Proofs.M09.OpenODEUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem regularizedCurve_eventuallyEq {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (γ δ : ℝ → M)
    (I : Set ℝ) (hI : IsOpen I) (htime : I ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ I)
    (hδ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ δ I)
    (Eγ : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (Eδ : ParametricAlongCurveExtensionOn (n := n) I δ (curveVelocityWithin (n := n) δ I))
    (heγ : ∀ s ∈ I, regularizedLGeodesicEquation F T γ I Eγ s)
    (heδ : ∀ s ∈ I, regularizedLGeodesicEquation F T δ I Eδ s)
    (s0 : ℝ) (hs0 : s0 ∈ I)
    (hphase : curvePhase (n := n) γ s0 = curvePhase (n := n) δ s0) :
    γ =ᶠ[𝓝 s0] δ := by
  let p := γ s0
  let e := chartAt V p
  have hbase : γ s0 = δ s0 := congrArg Bundle.TotalSpace.proj hphase
  have hvel : (curveVelocity γ s0 : V) = (curveVelocity δ s0 : V) :=
    congrArg (fun z : TangentBundle (𝓡 n) M ↦ (z.2 : V)) hphase
  let K := (I ∩ γ ⁻¹' e.source) ∩ (I ∩ δ ⁻¹' e.source)
  have hK : IsOpen K := (hγ.continuousOn.isOpen_inter_preimage hI e.open_source).inter
    (hδ.continuousOn.isOpen_inter_preimage hI e.open_source)
  have hsK : s0 ∈ K := by
    refine ⟨⟨hs0, mem_chart_source V p⟩, hs0, ?_⟩
    change δ s0 ∈ e.source
    rw [← hbase]
    exact mem_chart_source V p
  have hKI : K ⊆ I := fun _ ht ↦ ht.1.1
  have hγd : ∀ t ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ t :=
    fun t ht ↦ (hγ.contMDiffAt (hI.mem_nhds ht)).mdifferentiableAt (by simp)
  have hδd : ∀ t ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) δ t :=
    fun t ht ↦ (hδ.contMDiffAt (hI.mem_nhds ht)).mdifferentiableAt (by simp)
  let EγK := restrictVelocityExtension γ I K hKI hI.uniqueDiffOn hK.uniqueDiffOn hγd Eγ
  let EδK := restrictVelocityExtension δ I K hKI hI.uniqueDiffOn hK.uniqueDiffOn hδd Eδ
  let a : ℝ → V := fun t ↦ e (γ t)
  let c : ℝ → V := fun t ↦ e (δ t)
  let f : ℝ → V × V := fun t ↦ (a t, deriv a t)
  let g : ℝ → V × V := fun t ↦ (c t, deriv c t)
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
  have hf : ∀ t ∈ K, (t, f t) ∈ S ∧ HasDerivAt f (field (t, f t)) t := by
    intro t ht
    refine ⟨⟨htime (hKI ht), e.map_source ht.1.2⟩, ?_⟩
    exact regularizedCurve_chart_hasDerivAt F hM04 T b hb hwindow p γ K hK
      (hγ.mono hKI) (fun r hr ↦ hr.1.2) EγK t ht (htime (hKI ht))
      (regularizedEquation_restrict F T γ I K hKI hI.uniqueDiffOn hK.uniqueDiffOn
        hγd Eγ t ht (heγ t (hKI ht)))
  have hg : ∀ t ∈ K, (t, g t) ∈ S ∧ HasDerivAt g (field (t, g t)) t := by
    intro t ht
    refine ⟨⟨htime (hKI ht), e.map_source ht.2.2⟩, ?_⟩
    exact regularizedCurve_chart_hasDerivAt F hM04 T b hb hwindow p δ K hK
      (hδ.mono hKI) (fun r hr ↦ hr.2.2) EδK t ht (htime (hKI ht))
      (regularizedEquation_restrict F T δ I K hKI hI.uniqueDiffOn hK.uniqueDiffOn
        hδd Eδ t ht (heδ t (hKI ht)))
  have h0 : f s0 = g s0 := by
    apply Prod.ext
    · exact congrArg e hbase
    · change deriv a s0 = deriv c s0
      rw [(hasDerivAt_chart_curve p γ s0 hsK.1.2 (hγd s0 hs0)).deriv,
        (hasDerivAt_chart_curve p δ s0 hsK.2.2 (hδd s0 hs0)).deriv]
      exact congrArg₂ (fun (q : M) (v : V) ↦ (mfderiv (𝓡 n) (𝓡 n) e q) v) hbase hvel
  have hfg := openODE_eventuallyEq S hS field hfield f g s0 (hf s0 hsK).1 h0
    (Filter.Eventually.mono (hK.mem_nhds hsK) (fun t ht ↦ hf t ht))
    (Filter.Eventually.mono (hK.mem_nhds hsK) (fun t ht ↦ hg t ht))
  filter_upwards [hK.mem_nhds hsK, hfg] with t ht he
  exact e.injOn ht.1.2 ht.2.2 (congrArg Prod.fst he)

theorem regularizedCurve_phase_eqOn {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (γ δ : ℝ → M)
    (I : Set ℝ) (hI : IsOpen I) (hconn : IsPreconnected I)
    (htime : I ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ I)
    (hδ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ δ I)
    (Eγ : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (Eδ : ParametricAlongCurveExtensionOn (n := n) I δ (curveVelocityWithin (n := n) δ I))
    (heγ : ∀ s ∈ I, regularizedLGeodesicEquation F T γ I Eγ s)
    (heδ : ∀ s ∈ I, regularizedLGeodesicEquation F T δ I Eδ s)
    (s0 : ℝ) (hs0 : s0 ∈ I)
    (hphase : curvePhase (n := n) γ s0 = curvePhase (n := n) δ s0) :
    Set.EqOn (curvePhase (n := n) γ) (curvePhase (n := n) δ) I := by
  letI : T2Space (TangentBundle (𝓡 n) M) := tangentBundle_t2Space
  letI : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hconn
  let A : Set I := {s | curvePhase (n := n) γ s = curvePhase (n := n) δ s}
  have hclosed : IsClosed A := isClosed_eq
    (curvePhase_contMDiffOn γ I hI hγ).continuousOn.domRestrict
    (curvePhase_contMDiffOn δ I hI hδ).continuousOn.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal := regularizedCurve_eventuallyEq F hM04 T b hb hwindow γ δ I hI
      htime hγ hδ Eγ Eδ heγ heδ t t.property ht
    exact continuousAt_subtype_val.preimage_mem_nhds (curvePhase_eventuallyEq hlocal)
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨s0, hs0⟩, hphase⟩
  intro t ht
  have hm : (⟨t, ht⟩ : I) ∈ A := by rw [hAll]; trivial
  exact hm

end PoincareConjecture.Proofs.M09
