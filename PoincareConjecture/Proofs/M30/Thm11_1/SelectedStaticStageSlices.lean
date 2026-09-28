import PoincareConjecture.Proofs.M30.Thm11_1.StaticStageSliceMaps
import PoincareConjecture.Proofs.M30.Thm11_1.GoodSliceFiniteJets
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticStageMetricJets
import PoincareConjecture.Proofs.M30.Thm11_1.TerminalScalarConvergence
import PoincareConjecture.Proofs.M28.Mathlib.RelativeBilinearComparison
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.RelativeMetricReadout
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Finite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u w

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

variable (S : GeneralizedBlowupSequence.{u})
  (G : PartialPointedMetricConvergence (terminalComponentMetric S)
    (terminalComponentBase S) 1) (j N : ℕ)

local notation "Y" => (TopologicalSpace.Opens.mk (G.exhaustion j) (G.exhaustion_open j) :
  TopologicalSpace.Opens G.limitCarrier.carrier)
local notation "nu" => (fun k : ℕ => G.subsequence (k + N))
local notation "a" => (fun k : ℕ => Sigma.fst (S.base (nu k)))
local notation "Q" => (fun k : ℕ => S.scale (nu k))
local notation "b" => (fun (k : ℕ) (x : G.limitCarrier.carrier) =>
  Subtype.val (G.embedding (k + N) x))

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_good_static_stage_slice_sequence
    {W T B : ℝ} (hT : 0 < T)
    (E : ∀ k, ControlledBlowupCylinder S (nu k) W T B 1)
    (P : ℕ → RicciFlow 3 Y (Icc (-T) 0))
    (himage : ∀ k (x : Y), b k x.val ∈ S.baseBall (nu k) W)
    (hP : ∀ k s (hs : s ∈ Icc (-T) 0) (x : Y) (v w : TangentSpace (𝓡 3) x),
      ((P k).metric s).inner x v w = (E k).embedding.pullbackInner s hs
        (b k x.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => b k y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => b k y.val) x w))
    (hterminal : ∀ k (x : Y) (v w : TangentSpace (𝓡 3) x),
      ((P k).metric 0).inner x v w =
        (terminalComponentMetric S (nu k)).inner (G.embedding (k + N) x.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => G.embedding (k + N) y.val) x v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => G.embedding (k + N) y.val) x w))
    (D : LeviCivitaData G.limitMetric) (epsilon canonicalConstant : ℝ)
    (hdense : ∀ k, generalizedEarlierDenseStrongCanonicalNeighborhoods
      (S.flow (nu k)) epsilon canonicalConstant (a k) (S.base (nu k)).2)
    {ι : Type w} [Finite ι]
    (q : ι → G.limitCarrier.carrier)
    (U Kchart : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hU : ∀ i, IsOpen (U i))
    (hUtarget : ∀ i, U i ⊆ (extChartAt (𝓡 3) (q i)).target)
    (hKchart : ∀ i, IsCompact (Kchart i)) (hKU : ∀ i, Kchart i ⊆ U i)
    (psi : ι → EuclideanSpace ℝ (Fin 3) → Y)
    (hpsi : ∀ i, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (psi i) (U i))
    (hpsival : ∀ i z, z ∈ U i →
      (psi i z).val = (extChartAt (𝓡 3) (q i)).symm z)
    (K : Set G.limitCarrier.carrier) (hK : IsCompact K)
    (hKstage : K ⊆ G.exhaustion j)
    (hcover : K ⊆ ⋃ i, (extChartAt (𝓡 3) (q i)).symm '' Kchart i)
    (d : ℕ) (p : G.limitCarrier.carrier) {r R : ℝ}
    (hr : 0 < r) (hbuffer : 2 * r < R)
    (hball : closure (G.limitMetric.ball p R) ⊆ K) :
    ∃ s : ℕ → ℝ, ∃ hs : ∀ k, s k ∈ Icc (-T) 0,
      (∀ k : ℕ, -(1 / ((k : ℝ) + 1)) < s k) ∧
      (∀ k, a k + s k / Q k ∈ (S.flow (nu k)).interval ∧
        generalizedSliceStrongCanonicalNeighborhoods
          (S.flow (nu k)) epsilon canonicalConstant (4 * Q k)
          (a k + s k / Q k)) ∧
      (∀ k i m, m ≤ d → ∀ z ∈ Kchart i,
        ‖iteratedFDeriv ℝ m (((P k).metric (s k)).pullbackCoefficients (psi i)) z -
          iteratedFDeriv ℝ m (((P k).metric 0).pullbackCoefficients (psi i)) z‖ <
            1 / ((k : ℝ) + 1)) ∧
      (∀ k (x : Y), x.val ∈ K →
        |((P k).connection (s k)).scalarCurvature x -
          ((P k).connection 0).scalarCurvature x| < 1 / ((k : ℝ) + 1)) ∧
      let f := fun k (x : G.limitCarrier.carrier) =>
        (E k).embedding.forward (s k) (hs k) (b k x)
      let h : ∀ k, RiemannianMetric 3
          ((S.flow (nu k)).slice (a k + s k / Q k)).carrier := fun k => M13.scaleSmoothMetric
        ((S.flow (nu k)).metric (a k + s k / Q k)) (Q k) (S.base_scalar_pos (nu k))
      (∀ i m, m ≤ d → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          ((h k).pullbackCoefficients (f k ∘ (extChartAt (𝓡 3) (q i)).symm)))
        (iteratedFDeriv ℝ m
          (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
        atTop (Kchart i)) ∧
      TendstoUniformlyOn
        (fun k x => (S.flow (nu k)).scalar
          ((E k).embedding.pointMap (s k) (hs k) (b k x)) / Q k)
        D.scalarCurvature atTop K ∧
      (∀ᶠ k in atTop, ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3)
          G.limitCarrier.carrier
          ((S.flow (nu k)).slice (a k + s k / Q k)).carrier ∞,
        e.source = G.exhaustion j ∧
        (e : G.limitCarrier.carrier →
          ((S.flow (nu k)).slice (a k + s k / Q k)).carrier) = f k ∧
        e.target = f k '' G.exhaustion j ∧
        (h k).ball (f k p) r ⊆ f k '' G.limitMetric.ball p (2 * r)) := by
  classical
  let V := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let KY : Set Y := (Subtype.val : Y → G.limitCarrier.carrier) ⁻¹' K
  have hKY : IsCompact KY :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (fun x hx => ⟨⟨x, hKstage hx⟩, rfl⟩)
  have hchoose (k : ℕ) := exists_good_slice_with_finite_metric_jets
    (S.flow (nu k)) ((S.flow (nu k)).slice_nonempty_iff (a k) |>.mp
      ⟨(S.base (nu k)).2⟩) (S.base (nu k)).2 (hdense k)
    (S.base_scalar_pos (nu k)) hT (P k) U Kchart hU hKchart hKU psi hpsi
    KY hKY d (show 0 < 1 / ((k : ℝ) + 1) by positivity)
  choose s hs hsdelta hsI hgood hjet0 hscalar0 using hchoose
  let f := fun k (x : G.limitCarrier.carrier) =>
    (E k).embedding.forward (s k) (hs k) (b k x)
  let h : ∀ k, RiemannianMetric 3
      ((S.flow (nu k)).slice (a k + s k / Q k)).carrier := fun k => M13.scaleSmoothMetric
    ((S.flow (nu k)).metric (a k + s k / Q k)) (Q k) (S.base_scalar_pos (nu k))
  have hmaps (k : ℕ) (hk : j ≤ k + N) :=
    exists_static_stage_slice_partialDiffeomorph S G j N k hk hT (E k)
      (P k) (himage k) (hP k) (s k) (hs k)
  have hdelta : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hPjets (i : ι) (m : ℕ) (hm : m ≤ d) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (((P k).metric (s k)).pullbackCoefficients (psi i)))
      (iteratedFDeriv ℝ m
        (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
      atTop (Kchart i) := by
    have hzero := G.tendstoUniformlyOn_static_stage_metric_jets j N
      (fun k => (P k).metric 0) hterminal (q i) (U i) (hU i) (hUtarget i)
      (psi i) (hpsi i) (hpsival i) m (Kchart i) (hKchart i) (hKU i)
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eta heta
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hzero (eta / 2) (by positivity),
      hdelta.eventually (Iio_mem_nhds (show 0 < eta / 2 by positivity))]
      with k hk hdk z hz
    have hd : dist
        (iteratedFDeriv ℝ m (((P k).metric 0).pullbackCoefficients (psi i)) z)
        (iteratedFDeriv ℝ m (((P k).metric (s k)).pullbackCoefficients (psi i)) z)
        < eta / 2 := by
      have he := (hjet0 k i m hm z hz).trans hdk
      simpa only [dist_eq_norm, norm_sub_rev] using he
    have ht := dist_triangle
      (iteratedFDeriv ℝ m
        (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm) z)
      (iteratedFDeriv ℝ m (((P k).metric 0).pullbackCoefficients (psi i)) z)
      (iteratedFDeriv ℝ m (((P k).metric (s k)).pullbackCoefficients (psi i)) z)
    have hz0 := hk z hz
    linarith
  have hjets (i : ι) (m : ℕ) (hm : m ≤ d) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        ((h k).pullbackCoefficients (f k ∘ (extChartAt (𝓡 3) (q i)).symm)))
      (iteratedFDeriv ℝ m
        (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
      atTop (Kchart i) := by
    apply (hPjets i m hm).congr
    filter_upwards [eventually_ge_atTop j] with k hk
    obtain ⟨e, hes, hef, _, hmetric, _⟩ := hmaps k (by omega)
    change (e : G.limitCarrier.carrier → _) = f k at hef
    change ∀ (x : Y) (v w : TangentSpace (𝓡 3) x),
      ((P k).metric (s k)).inner x v w = (h k).inner (e x.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => e y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => e y.val) x w) at hmetric
    let F : Y → ((S.flow (nu k)).slice (a k + s k / Q k)).carrier :=
      fun y => e y.val
    have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F := by
      intro y
      have hys : y.val ∈ e.source := hes.symm ▸ y.property
      exact ((e.contMDiffOn y.val hys).contMDiffAt (e.open_source.mem_nhds hys)).comp y
        (contMDiff_subtype_val (U := Y) (n := ∞) y)
    have heq : EqOn (((P k).metric (s k)).pullbackCoefficients (psi i))
        ((h k).pullbackCoefficients (f k ∘ (extChartAt (𝓡 3) (q i)).symm)) (U i) := by
      intro z hz
      have hpsiAt := (hpsi i z hz).contMDiffAt ((hU i).mem_nhds hz)
      have hnear : F ∘ psi i =ᶠ[𝓝 z] f k ∘ (extChartAt (𝓡 3) (q i)).symm := by
        filter_upwards [(hU i).mem_nhds hz] with y hy
        change e (psi i y).val = f k ((extChartAt (𝓡 3) (q i)).symm y)
        rw [hpsival i y hy, hef]
      have hd := (mfderiv_comp z ((hF (psi i z)).mdifferentiableAt (by simp))
        (hpsiAt.mdifferentiableAt (by simp))).symm.trans hnear.mfderiv_eq
      ext v w
      change ((P k).metric (s k)).inner (psi i z)
        (mfderiv (𝓡 3) (𝓡 3) (psi i) z v)
        (mfderiv (𝓡 3) (𝓡 3) (psi i) z w) = _
      rw [hmetric]
      have hp := hnear.self_of_nhds
      change e (psi i z).val = f k ((extChartAt (𝓡 3) (q i)).symm z) at hp
      erw [congrArg (fun L => L v) hd, congrArg (fun L => L w) hd, hp]
      rfl
    intro z hz
    have hnear : ((P k).metric (s k)).pullbackCoefficients (psi i) =ᶠ[𝓝 z]
        (h k).pullbackCoefficients (f k ∘ (extChartAt (𝓡 3) (q i)).symm) := by
      filter_upwards [(hU i).mem_nhds (hKU i hz)] with y hy
      exact heq hy
    exact (hnear.iteratedFDeriv ℝ m).self_of_nhds
  have hzeroScalar (k : ℕ) (hk : j ≤ k + N) (x : Y) :
      ((P k).connection 0).scalarCurvature x =
        (S.flow (nu k)).scalar ⟨a k, b k x.val⟩ / Q k := by
    let F : Y → (terminalComponentCarrier S (nu k)).carrier :=
      fun y => G.embedding (k + N) y.val
    have hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F := by
      intro y
      exact ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y y).comp (𝓡 3)
        (terminalComponentCarrier S (nu k)).carrier
        (G.embedding_smooth (k + N)
          ⟨y.val, G.exhaustion_monotone hk y.property⟩)).contMDiffAt
    have hread := ((P k).connection 0).scalarCurvature_eq_of_local_isometry
      (terminalComponentMetric S (nu k)).leviCivitaData isOpen_univ hF.contMDiffOn
      (fun y _ v w => hterminal k y v w) (mem_univ x)
    exact hread.trans (terminalComponentMetric_scalarCurvature S (nu k) _ (F x))
  have hscalar : TendstoUniformlyOn
      (fun k x => (S.flow (nu k)).scalar
        ((E k).embedding.pointMap (s k) (hs k) (b k x)) / Q k)
      D.scalarCurvature atTop K := by
    have hterminalConv := tendstoUniformlyOn_terminal_normalized_scalar S G D K hK
    have hshift : TendstoUniformlyOn
        (fun k x => (S.flow (nu k)).scalar ⟨a k, b k x⟩ / Q k)
        D.scalarCurvature atTop K :=
      fun L hL => (tendsto_add_atTop_nat N).eventually (hterminalConv L hL)
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eta heta
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hshift (eta / 2) (by positivity),
      hdelta.eventually (Iio_mem_nhds (show 0 < eta / 2 by positivity)),
      eventually_ge_atTop j] with k hk hdk hjk x hx
    let y : Y := ⟨x, hKstage hx⟩
    obtain ⟨_, _, _, _, _, hread⟩ := hmaps k (by omega)
    have hdiff : |(S.flow (nu k)).scalar
        ((E k).embedding.pointMap (s k) (hs k) (b k x)) / Q k -
        (S.flow (nu k)).scalar ⟨a k, b k x⟩ / Q k| < 1 / ((k : ℝ) + 1) := by
      rw [← hread y, ← hzeroScalar k (by omega) y]
      exact hscalar0 k y hx
    have hd : dist ((S.flow (nu k)).scalar ⟨a k, b k x⟩ / Q k)
        ((S.flow (nu k)).scalar
          ((E k).embedding.pointMap (s k) (hs k) (b k x)) / Q k) < eta / 2 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hdiff.trans hdk
    have ht := dist_triangle (D.scalarCurvature x)
      ((S.flow (nu k)).scalar ⟨a k, b k x⟩ / Q k)
      ((S.flow (nu k)).scalar
        ((E k).embedding.pointMap (s k) (hs k) (b k x)) / Q k)
    have hx0 := hk x hx
    linarith
  have hcompare (i : ι) : ∀ᶠ k in atTop, ∀ z ∈ Kchart i, ∀ v : V,
      (1 / 4 : ℝ) * G.limitMetric.pullbackCoefficients
          (extChartAt (𝓡 3) (q i)).symm z v v ≤
        (h k).pullbackCoefficients (f k ∘ (extChartAt (𝓡 3) (q i)).symm) z v v ∧
      (h k).pullbackCoefficients (f k ∘ (extChartAt (𝓡 3) (q i)).symm) z v v ≤
        4 * G.limitMetric.pullbackCoefficients
          (extChartAt (𝓡 3) (q i)).symm z v v := by
    let c := extChartAt (𝓡 3) (q i)
    have hct : Kchart i ⊆ c.target := (hKU i).trans (hUtarget i)
    have hc (z : V) (hz : z ∈ c.target) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
      (contMDiffOn_extChartAt_symm (q i)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) (q i)).mem_nhds hz)
    have hcont : ContinuousOn (G.limitMetric.pullbackCoefficients c.symm) (Kchart i) :=
      fun z hz => (G.limitMetric.contDiffAt_pullbackCoefficients
        (hc z (hct hz))).continuousAt.continuousWithinAt
    have hpos : ∀ z ∈ Kchart i, ∀ v : V, v ≠ 0 →
        0 < G.limitMetric.pullbackCoefficients c.symm z v v := by
      intro z hz v hv
      have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible :=
        Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm (hct hz)
      apply G.limitMetric.pos
      intro hzero
      apply hv
      apply hi.injective
      rw [map_zero]
      exact hzero
    obtain ⟨alpha, halpha, hlower⟩ :=
      exists_uniform_bilinear_family_lower_bound (hKchart i) hcont hpos
    have hcoeff : TendstoUniformlyOn
        (fun k => (h k).pullbackCoefficients (f k ∘ c.symm))
        (G.limitMetric.pullbackCoefficients c.symm) atTop (Kchart i) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using!
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → V)).comp_tendstoUniformlyOn (hjets i 0 (Nat.zero_le d))
    filter_upwards [(Metric.tendstoUniformlyOn_iff
      (α := V →L[ℝ] V →L[ℝ] ℝ)).mp hcoeff ((3 / 4) * alpha) (by positivity)]
      with k hk z hz v
    have he := ContinuousLinearMap.relative_quadratic_bounds_of_norm_sub_le
      (G.limitMetric.pullbackCoefficients c.symm z)
      ((h k).pullbackCoefficients (f k ∘ c.symm) z) halpha
      (show (0 : ℝ) < 3 by norm_num) (hlower z hz)
      (by simpa only [show (3 : ℝ) / (1 + 3) = 3 / 4 by norm_num,
        dist_eq_norm, norm_sub_rev] using (hk z hz).le) v
    norm_num at he
    exact he
  refine ⟨s, hs, hsdelta, ?_, hjet0, ?_, hjets, hscalar, ?_⟩
  · intro k
    exact ⟨hsI k, hgood k⟩
  · intro k x hx
    exact hscalar0 k x hx
  · have hall := Filter.eventually_all.mpr hcompare
    filter_upwards [hall, eventually_ge_atTop j] with k hk hjk
    obtain ⟨e, hes, hef, het, _, _⟩ := hmaps k (by omega)
    change (e : G.limitCarrier.carrier → _) = f k at hef
    refine ⟨e, hes, hef, het, ?_⟩
    let eH := e.toOpenPartialHomeomorph
    have hsource : closure (G.limitMetric.ball p R) ⊆ eH.source := by
      change closure (G.limitMetric.ball p R) ⊆ e.source
      rw [hes]
      exact hball.trans hKstage
    have hnorm : ∀ x ∈ closure (G.limitMetric.ball p R), ∀ v : TangentSpace (𝓡 3) x,
        G.limitMetric.tangentNorm x v ≤
          2 * (h k).tangentNorm (eH x) (mfderiv (𝓡 3) (𝓡 3) eH x v) := by
      intro x hx v
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp (hcover (hball hx))
      let c := extChartAt (𝓡 3) (q i)
      have hzt : z ∈ c.target := hUtarget i (hKU i hz)
      have hxc : x ∈ c.source := hzx ▸ c.map_target hzt
      have hcx : c x = z := by rw [← hzx]; exact c.right_inv hzt
      have hdiff : MDifferentiableAt (𝓡 3) (𝓡 3) (f k) x := by
        rw [← hef]
        exact ((e.contMDiffOn x (hsource hx)).contMDiffAt
          (e.open_source.mem_nhds (hsource hx))).mdifferentiableAt (by simp)
      have hrel := RiemannianMetric.relative_inner_bounds_of_chart G.limitMetric (h k)
        hxc hdiff (fun w => by rw [hcx]; exact hk i z hz w) v
      have henergy : G.limitMetric.inner x v v ≤
          4 * (h k).inner (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
            (mfderiv (𝓡 3) (𝓡 3) (f k) x v) := by
        linarith [hrel.1]
      change G.limitMetric.tangentNorm x v ≤
        2 * (h k).tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
      rw [hef]
      calc
        G.limitMetric.tangentNorm x v ≤ Real.sqrt
            (4 * (h k).inner (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
              (mfderiv (𝓡 3) (𝓡 3) (f k) x v)) := Real.sqrt_le_sqrt henergy
        _ = 2 * (h k).tangentNorm (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num [RiemannianMetric.tangentNorm]
    have hdiff : eH.MDifferentiable (𝓡 3) (𝓡 3) :=
      ⟨e.contMDiffOn.mdifferentiableOn (by simp),
        e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
    have hinverse := G.limitMetric.inverse_tangentNorm_le_of_le (h k) eH hdiff hsource hnorm
    have hcapture := G.limitMetric.ball_subset_image_ball_of_inverse_tangentNorm_le
      (h k) eH p (by linarith : 0 < R) (by norm_num : (0 : ℝ) < 2) hbuffer
      (hK.of_isClosed_subset isClosed_closure hball) hsource
      (fun y hy => ((e.symm.contMDiffOn y hy).contMDiffAt
        (e.open_target.mem_nhds hy)).of_le (by simp)) hinverse
    change (h k).ball (e p) r ⊆ e '' G.limitMetric.ball p (2 * r) at hcapture
    simpa only [hef] using hcapture

end PoincareConjecture.M30
