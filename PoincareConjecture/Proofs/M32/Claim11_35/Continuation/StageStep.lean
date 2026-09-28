import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.CompactCapture
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.RegularNecks
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.StageControls
import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.NoncollapseGluing
import PoincareConjecture.Proofs.M32.Claim11_32.SequenceReindex
import PoincareConjecture.Proofs.M32.Claim11_32.NeckVolume
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.TerminalPinching
import PoincareConjecture.Proofs.M32.Mathlib.EventualSubsequence
import PoincareConjecture.Proofs.M32.Claim11_34.TerminalAnnuli
import PoincareConjecture.Proofs.M32.Claim11_34.LimitLine
import PoincareConjecture.Proofs.M32.Claim11_35.CompactProductFactor
import PoincareConjecture.Proofs.M32.Claim11_35.SurfacePositivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local macro "stage[" S:term "," T:term "," M:term "," B:term "]" : term =>
  `(∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta → ∀ᶠ k : ℕ in atTop,
    ∃ e : ControlledBlowupCylinder $S k A $T $B eta,
      (∀ s hs y, y ∈ ($S).baseBall k A →
        (($S).flow k).scalar (e.embedding.pointMap s hs y) ≤ $M * ($S).scale k) ∧
      (∀ s hs y, y ∈ ($S).baseBall k A → GeneralizedKappaNoncollapsedAt
        (($S).flow k) (e.embedding.pointMap s hs y) neckNoncollapseConstant 1))

theorem exists_terminalBlowupSequence_noncollapsed_stage_step
    (P : RepairedHornSelectionPredecessors.{u}) :
    ∃ epsilonStep Kstep : ℝ, 0 < epsilonStep ∧ epsilonStep ≤ 1 / 200 ∧ 0 < Kstep ∧
      ∀ {Mbound B c T : ℝ}, 0 < Mbound → 0 ≤ B → Kstep * Mbound ≤ B →
        0 < c → c ≤ 1 / (4 * Mbound) → c ≤ T →
      ∀ {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
        [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
        [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
        [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
        [∀ k, SecondCountableTopology (M k)]
        {F : ℕ → GeneralizedRicciFlowData.{u}} {terminal : ℕ → ℝ}
        (H : ∀ k, SingularTimeAssumptions (F k) (terminal k) (M k))
        (Q : ∀ k, SingularLimitConclusion (H k))
        (x : ∀ k, ((Q k).extension.extended.slice (terminal k)).carrier)
        (hpos : ∀ k, 0 < ((Q k).extension.extended.connection
          (terminal k)).scalarCurvature (x k))
        (hdiv : Tendsto (fun k => ((Q k).extension.extended.connection
          (terminal k)).scalarCurvature (x k)) atTop atTop)
        (A_top : RepairedNeckCapTopologyTheory.{u}) {Kcut Banalytic Ccap : ℝ},
        0 < Kcut → 0 < Banalytic → 0 < Ccap →
        (∀ k, (H k).r₀⁻¹ ^ 2 < Kcut) →
        (∀ k, (H k).analytic_constant = Banalytic) →
        (∀ k, (H k).constant ≤ Ccap) →
        (∀ k, terminalAccuracyFactor * (H k).epsilon ≤ epsilonStep) →
        (∀ k, terminalAccuracyFactor * (H k).epsilon ≤ A_top.epsilon₀) →
      ∀ horn : ∀ k, StrongHorn (Q k).extension (terminalAccuracyFactor * (H k).epsilon),
        (∀ k, x k ∈ (horn k).carrier) →
        (∀ k, ∀ y ∈ (horn k).boundary_sphere,
          ((Q k).extension.extended.connection (terminal k)).scalarCurvature y ≤ Kcut) →
        BlowupBaseBallsCompact (terminalBlowupSequence H Q x hpos hdiv) →
        stage[terminalBlowupSequence H Q x hpos hdiv, T, Mbound, B] →
        stage[terminalBlowupSequence H Q x hpos hdiv, T + c, Mbound, B] := by
  classical
  obtain ⟨epsilonGlue, Kstep, hGlue, hGlueSmall, hKstep, hglue⟩ :=
    exists_noncollapsed_cylinder_backward_extension_of_strongNecks P.m04
  obtain ⟨epsilonRegular, hRegular, _hRegularSmall, hregularNecks⟩ :=
    exists_terminalBlowupConvergence_regular_slice_necks.{u, u}
  obtain ⟨epsilonAnnulus, hAnnulus, _hAnnulusSmall, hannuli⟩ :=
    terminalBlowupSequence_eventually_horn_annulus_separation.{u}
  let epsilonStep := min epsilonGlue (min epsilonRegular epsilonAnnulus)
  refine ⟨epsilonStep, Kstep, lt_min hGlue (lt_min hRegular hAnnulus),
    (min_le_left _ _).trans hGlueSmall, hKstep, ?_⟩
  intro Mbound B c T hM hB hKM hc hcM hcT M _ _ _ _ _ _ _ _ F terminal
    H Q x hpos hdiv A_top Kcut Banalytic Ccap hKcut hBanalytic hCcap hcutoff
    hanalytic hconstant hepsilon htop horn hx hboundary hballs hstage
  let S := terminalBlowupSequence H Q x hpos hdiv
  have hT : 0 < T := hc.trans_le hcT
  have hepsilonOriginal (i : ℕ) : (H i).epsilon ≤ terminalAccuracyFactor * (H i).epsilon := by
    have hf : 1 ≤ terminalAccuracyFactor := le_trans (by norm_num) two_le_terminalAccuracyFactor
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hf (H i).epsilon_pos.le
  have hGlueEps (i : ℕ) : (H i).epsilon ≤ epsilonGlue :=
    (hepsilonOriginal i).trans ((hepsilon i).trans (min_le_left _ _))
  have hRegularEps (i : ℕ) : (H i).epsilon ≤ epsilonRegular :=
    (hepsilonOriginal i).trans
      ((hepsilon i).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨a, hawindow, hcatalog⟩ := exists_common_regular_normalized_time H S.scale
    S.base_scalar_pos (show -T + c / 2 < -T + 3 * c / 4 by linarith)
  have ha : -T < a := by linarith [hawindow.1]
  have hac : a ≤ -T + c := by linarith [hawindow.2]
  have haNeg : a < 0 := by linarith [hawindow.2]
  have haOld : a ∈ Icc (-T) 0 := ⟨ha.le, haNeg.le⟩
  choose N hN using fun i => (horn i).every_point_neck (x i) (hx i)
  intro A hA eta heta
  apply eventually_atTop_of_forall_subseq
  intro phi hphi
  let Sphi := blowupSequenceComp S phi hphi
  have hballsPhi : BlowupBaseBallsCompact Sphi :=
    fun R hR => hphi.tendsto_atTop.eventually (hballs R hR)
  have hstagePhi : stage[Sphi, T, Mbound, B] := by
    intro R hR delta hdelta
    filter_upwards [hphi.tendsto_atTop.eventually (hstage R hR delta hdelta)] with k hk
    obtain ⟨e, hscalar, hnoncollapse⟩ := hk
    let e' : ControlledBlowupCylinder Sphi k R T B delta := {
      embedding := e.embedding
      zero_identity := e.zero_identity
      curvature_bound := e.curvature_bound
      negative_curvature_bound := e.negative_curvature_bound }
    exact ⟨e', hscalar, hnoncollapse⟩
  have hvolume := terminal_volume_of_strongNecks Sphi (Filter.Eventually.of_forall fun i => by
    refine ⟨terminalAccuracyFactor * (H (phi i)).epsilon, ?_, N (phi i), hN (phi i)⟩
    exact ((hepsilon (phi i)).trans ((min_le_left _ _).trans hGlueSmall)).trans_lt
      (by norm_num))
  have hgeometric : M30GeometricLongControls Sphi (ENNReal.ofReal T) :=
    geometricLongControls_of_closed_cylinders Sphi hT hB hballsPhi hvolume
      (fun R hR delta hdelta => (hstagePhi R hR delta hdelta).mono
        fun _ hi => ⟨hi.choose⟩)
  obtain ⟨G⟩ := P.m30.geometric_long Sphi (ENNReal.ofReal T) hgeometric
  have haJ : a ∈ blowupBackwardInterval (ENNReal.ofReal T) :=
    ⟨haNeg.le, (ENNReal.ofReal_lt_ofReal_iff hT).mpr (by linarith)⟩
  have hAnnulusEps (i : ℕ) : terminalAccuracyFactor * (H (phi i)).epsilon ≤ epsilonAnnulus :=
    (hepsilon (phi i)).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hSphere, hAnnuli⟩ := hannuli
    (M := fun i => M (phi i)) (F := fun i => F (phi i))
    (T := fun i => terminal (phi i)) (fun i => H (phi i)) (fun i => Q (phi i))
    (fun i => x (phi i)) (fun i => hpos (phi i)) (hdiv.comp hphi.tendsto_atTop)
    P.m04 A_top hKcut hBanalytic (fun i => hcutoff (phi i))
    (fun i => hanalytic (phi i)) hAnnulusEps (fun i => htop (phi i))
    (fun i => horn (phi i)) (fun i => hx (phi i)) (fun i => hboundary (phi i))
    (fun i => N (phi i)) (fun i => hN (phi i)) hballsPhi
  obtain ⟨hSeparator, gamma, _hgammaContinuous, hgamma, _hanchor, hseparated⟩ :=
    blowup_exists_minimizing_line_and_compact_separator G
      (fun i => (N (phi i)).central_sphere)
      (show 0 < 2 * Real.pi + 1 by positivity) (Filter.Eventually.of_forall hSphere)
      (show 0 ≤ 2 * Real.pi + 3 by positivity) hAnnuli
  have hbuffer : 0 < T - c / 4 := by linarith
  have hbufferJ : Icc (-(T - c / 4)) 0 ⊆ blowupBackwardInterval (ENNReal.ofReal T) := by
    intro s hs
    exact ⟨hs.2, (ENNReal.ofReal_lt_ofReal_iff hT).mpr (by linarith [hs.1])⟩
  obtain ⟨_Blimit, _hBlimit, _hcurvature, C, hCcompact, H2, _hcomplete,
      hnonnegative, _hsurfaceCurvature, Phi, _hheight, hproduct, hscalarProduct,
      _hcurvatureProduct, hterminalScalar⟩ :=
    blowupLimit_exists_compact_product_on_closed_slab P G.limit hbuffer hbufferJ gamma
      hgamma hSeparator (fun t ht => (hseparated t ht).2.2)
  let : CompactSpace C.carrier := hCcompact
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  have haBuffer : a ∈ Icc (-(T - c / 4)) 0 := ⟨by linarith [hawindow.1], haNeg.le⟩
  have hpositive : ∀ z, 0 < (G.limit.flow.connection a).scalarCurvature z := by
    intro z
    rw [← hscalarProduct a haBuffer z]
    exact compact_surface_scalar_positive_on_Ioc (by linarith : -(T - c / 4) < 0)
      H2 hnonnegative (Phi.symm G.limit.base).1 (by rw [hterminalScalar]; norm_num)
      a ⟨by linarith [hawindow.1], haNeg.le⟩ (Phi.symm z).1
  obtain ⟨K, hK, hcapture⟩ :=
    blowup_exists_compact_capture_for_old_cylinders G hA haJ haOld
  have hnecks := hregularNecks
    (M := fun i => M (phi i)) (F := fun i => F (phi i))
    (T := fun i => terminal (phi i)) (fun i => H (phi i)) (fun i => Q (phi i))
    (fun i => x (phi i)) (fun i => hpos (phi i)) (hdiv.comp hphi.tendsto_atTop)
    G haJ haNeg hKcut hCcap (fun i => hcutoff (phi i))
    (fun i => hconstant (phi i)) (fun i => hRegularEps (phi i))
    (fun i => hcatalog (phi i)) (H2.metric a) Phi (hproduct a haBuffer)
    hK (fun z _ => hpositive z)
  refine ⟨G.subsequence, G.subsequence_strictMono, ?_⟩
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
      (hstagePhi (A + 1) (by linarith) 1 zero_lt_one),
    G.subsequence_strictMono.tendsto_atTop.eventually (hballsPhi A hA),
    hcapture, hnecks,
    (Sphi.scalar_diverges.comp G.subsequence_strictMono.tendsto_atTop).eventually
      (eventually_ge_atTop (Real.exp (4 + Mbound / (2 * eta)) / eta))]
    with k hold hcompact hcaptureK hnecksK hscale
  obtain ⟨old, holdScalar, holdNoncollapse⟩ := hold
  obtain ⟨hak, _hKsource, hmatch⟩ := hcaptureK
  obtain ⟨_, _hsource, hneck⟩ := hnecksK
  let i := G.subsequence k
  have hattachment : ∀ y ∈ closure (Sphi.baseBall i A), ∃ epsilon, epsilon ≤ epsilonGlue ∧
      ∃ N' : GeneralizedStrongNeck (Sphi.flow i)
        ((Sphi.base i).1 + a / Sphi.scale i) epsilon,
        N'.center = old.embedding.forward a haOld y := by
    intro y hy
    obtain ⟨z, hz, hsame⟩ := hmatch B 1 old y hy
    obtain ⟨N', hcenter⟩ := hneck z hz
    refine ⟨(H (phi i)).epsilon, hGlueEps (phi i), N', ?_⟩
    have hforward : old.embedding.forward a haOld y =
        (G.embedding k).forward a hak z := eq_of_heq (Sigma.mk.inj_iff.mp hsame).2
    exact hcenter.trans hforward.symm
  let gsource := (Sphi.flow i).metric (Sphi.base i).1
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : ((Sphi.flow i).slice (Sphi.base i).1).carrier → Type _) :=
    ⟨gsource.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : ((Sphi.flow i).slice (Sphi.base i).1).carrier → Type _) :=
    ⟨⟨gsource.inner, gsource.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace ((Sphi.flow i).slice (Sphi.base i).1).carrier :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) _
  have hq : 0 < Sphi.scale i := Sphi.base_scalar_pos i
  have hsqrt : 0 < Real.sqrt (Sphi.scale i) := Real.sqrt_pos.mpr hq
  have hU : IsOpen (Sphi.baseBall i A) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hW : IsOpen (Sphi.baseBall i (A + 1)) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hnonempty : (Sphi.baseBall i A).Nonempty := by
    refine ⟨(Sphi.base i).2, ?_⟩
    change edist (Sphi.base i).2 (Sphi.base i).2 < ENNReal.ofReal (A / Real.sqrt (Sphi.scale i))
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr (div_pos hA hsqrt)
  have hKW : closure (Sphi.baseBall i A) ⊆ Sphi.baseBall i (A + 1) := by
    have hclosed : closure (Sphi.baseBall i A) ⊆
        {y | gsource.edist (Sphi.base i).2 y ≤ ENNReal.ofReal (A / Real.sqrt (Sphi.scale i))} := by
      apply closure_minimal
      · intro y hy
        exact (show gsource.edist (Sphi.base i).2 y <
          ENNReal.ofReal (A / Real.sqrt (Sphi.scale i)) from hy).le
      · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
    intro y hy
    exact (hclosed hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (div_pos (show 0 < A + 1 by linarith) hsqrt)).mpr
      ((div_lt_div_iff_of_pos_right hsqrt).mpr (by linarith)))
  obtain ⟨g, hgold, hgscalar, hgcurvature, hgnoncollapse⟩ :=
    hglue hM hB hKM hc hcM old.embedding hU hW hnonempty hcompact hKW
      hcT ha hac holdScalar old.curvature_bound holdNoncollapse hattachment
  let next : ControlledBlowupCylinder S (phi i) A (T + c) B eta := {
    embedding := g
    zero_identity := by
      intro hzero y hy
      have hzeroOld : (0 : ℝ) ∈ Icc (-T) 0 := ⟨neg_nonpos.mpr hT.le, le_rfl⟩
      rw [hgold 0 hzeroOld y hy]
      exact old.zero_identity hzeroOld y (hKW (subset_closure hy))
    curvature_bound := hgcurvature
    negative_curvature_bound := fun s hs y hy =>
      negativeCurvaturePart_le_of_pinched_scalar_bound
        (extension_pinchedOrNonnegative P.m04 (H (phi i)) (Q (phi i)).extension)
        hM hq heta hscale (g.pointMap s hs y) (hgscalar s hs y hy) }
  exact ⟨next, hgscalar, hgnoncollapse⟩

end PoincareConjecture.M32
