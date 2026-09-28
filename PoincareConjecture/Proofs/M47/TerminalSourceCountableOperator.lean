import PoincareConjecture.Proofs.M47.TerminalSourceCountableFlowPatch
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourcePinching
import PoincareConjecture.Proofs.M47.TerminalGermsPinchedOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter TopologicalSpace Poincare.Gluing
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

theorem terminalSourceCountable_chart_operator
    (U : ℕ → Opens E) [∀ i, Nonempty (U i)] (i j : ℕ)
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (P : M46Predecessors.{u})
    {tau R L eta : ℝ} (htau : 0 < tau) (hUR : (U i : Set E) ⊆ Metric.ball 0 R)
    (F0 : {k : ℕ // j ≤ k} → SurgeryFlowData.{u})
    (O : ∀ a, SurgeryObservation (F0 a))
    (W : ∀ a, M33RegularHistoryWindow (F0 a))
    (H : ∀ a, M33RegularHistoryData (W a))
    (C0 : {k : ℕ // j ≤ k} → GeneralizedSliceCarrier.{u})
    (base Q rNext : {k : ℕ // j ≤ k} → ℝ)
    (source : ∀ a, Opens (C0 a).carrier)
    (cyl : ∀ a, GeneralizedFlowCylinder (H a).generalized (C0 a)
      (base a) (Q a) (Icc (-tau) 0) (source a))
    (F : ∀ a, RicciFlow 3 (source a) (Icc (-tau) 0))
    (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)
    (hGood : ∀ᶠ a in Filter.comap
        (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop,
      TerminalSourceJetsG4Good S B p (O a) (H a) (source a) (cyl a) (F a)
        (L := L) (eta := eta) (rNext := rNext a) (C a))
    (hmetric : ∀ a (s : ℝ) (hs : s ∈ Icc (-tau) 0) (x : source a),
      ∀ v w : TangentSpace (𝓡 3) x,
        ((F a).metric s).inner x v w = (cyl a).pullbackInner s hs x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : source a → (C0 a).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : source a → (C0 a).carrier) x w))
    (hQ : Tendsto Q (Filter.comap (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop) atTop)
    (f0 : ℕ → E → V) {sigma : ℕ → ℕ} (hsigma : StrictMono sigma)
    (coeff : ℝ × E → V)
    (G : letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
      RicciFlow 3 (U i) (Icc (-(tau / 4)) 0))
    (hcoeff : letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
      ∀ t ∈ Icc (-(tau / 4)) 0, ∀ (x : U i) v w,
        (G.metric t).inner x v w = coeff (t, x) v w)
    (hjet : ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 4)) 0 ×ˢ (U i : Set E) →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
        (terminalSourceCountableNegative j (fun a => (source a : Type u)) F C f0 (sigma k)))
        (iteratedFDeriv ℝ m coeff) atTop K) :
    letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc (-(tau / 4)) 0, ∀ x,
      (G.connection t).NonnegativeCurvatureOperator x := by
  let index := fun k => terminalSourceCountableSourceIndex j (sigma k)
  let patch := fun k => terminalSourceCountableSourceFlow j
    (fun a => (source a : Type u)) htau F (sigma k)
  let phi := fun (k : ℕ) (x : U i) => (C (index k)).chart x.val
  have hphi (k : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (phi k) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U i) x).comp (𝓡 3) _
      ((C (index k)).chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        ((C (index k)).source.symm ▸ hUR x.property))
  let seq := fun (k : ℕ) (z : ℝ × E) => ((patch k).metric z.1).pullbackCoefficients
    (ChartDistance.chartParametrization (fun n => (U n : Set E))
      (fun n => (U n).isOpen) (phi k)) z.2
  have hread (k : ℕ) (t : ℝ) : EqOn (fun x => seq k (t, x))
      (((patch k).metric t).pullbackCoefficients (C (index k)).chart) (U i) :=
    terminalSourceCountable_pullback_readout U ((patch k).metric t)
      ((patch k).metric t) (hphi k).contMDiff (C (index k)).chart
      ((C (index k)).smooth.mono hUR) (fun _ _ _ => rfl)
  have heq : ∀ᶠ k in atTop, EqOn (seq k)
      (terminalSourceCountableNegative j (fun a => (source a : Type u)) F C f0 (sigma k))
      (univ ×ˢ (U i : Set E)) := by
    filter_upwards [terminalSourceCountableSourceFlow_eventually_coefficients j
      (fun a => (source a : Type u)) htau F C f0 hsigma] with k hk z hz
    exact (hread k z.1 hz.2).trans (congrFun hk z)
  have hseqjet : ∀ m K, IsCompact K → K ⊆ Ioo (-(tau / 4)) 0 ×ˢ (U i : Set E) →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (seq k))
        (iteratedFDeriv ℝ m coeff) atTop K := by
    intro m K hK hKU
    apply (hjet m K hK hKU).congr
    filter_upwards [heq] with k hk z hz
    have hgerm : seq k =ᶠ[𝓝 z]
        terminalSourceCountableNegative j (fun a => (source a : Type u)) F C f0 (sigma k) := by
      filter_upwards [(isOpen_univ.prod (U i).isOpen).mem_nhds
        (show z ∈ univ ×ˢ (U i : Set E) from ⟨mem_univ _, (hKU hz).2⟩)] with y hy
      exact hk hy
    exact ((hgerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds).symm
  have hsectional := terminalCurvature_eventually_source_sectional
    (Filter.comap (Subtype.val : {k : ℕ // j ≤ k} → ℕ) atTop)
    S B p P F0 O W H C0 base Q rNext source cyl F C hGood hmetric hQ
  have hlower : ∀ error : ℝ, 0 < error → ∀ᶠ k in atTop,
      ∀ t ∈ Icc (-(tau / 4)) 0, ∀ (x : source (index k)) (v w : TangentSpace (𝓡 3) x),
        -error ≤ ((patch k).connection t).sectionalCurvature x v w := by
    intro error herror
    have hnat := Filter.eventually_comap.mp (hsectional error herror)
    filter_upwards [hsigma.tendsto_atTop.eventually hnat,
      hsigma.tendsto_atTop.eventually (eventually_ge_atTop j)] with k hk hjk t ht x v w
    have hindex : (index k).val = sigma k := max_eq_left hjk
    exact hk (index k) hindex t ⟨by linarith [ht.1], ht.2⟩ x v w
  have hphiCanonical : letI := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (phi k) := by
    rw [canonicalDomain_chartedSpace_eq_opens]
    exact hphi
  let := (U i).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (U i).isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  exact terminalGerms_operator_of_original_chart_jets
    (fun n => (U n : Set E)) (fun n => (U n).isOpen) (by linarith : -(tau / 4) < 0)
    patch i phi hphiCanonical G coeff hcoeff hseqjet hlower

end PoincareConjecture.M47
