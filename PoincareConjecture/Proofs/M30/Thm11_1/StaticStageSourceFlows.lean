import PoincareConjecture.Proofs.M30.Thm11_1.TerminalComponentGeometry
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.CompactImageBounds
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ComponentSourcePullback
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ControlledSource
import PoincareConjecture.Proofs.M30.Thm3_28.TerminalBuffer











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable




theorem exists_source_flows_on_static_stage
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S)
    (G : PartialPointedMetricConvergence
      (terminalComponentMetric S) (terminalComponentBase S) 1)
    (hcomplete : G.limitCarrier.metricComplete G.limitMetric) (j : ℕ) :
    let Y : TopologicalSpace.Opens G.limitCarrier.carrier :=
      ⟨G.exhaustion j, G.exhaustion_open j⟩
    ∃ W T B : ℝ, 0 < W ∧ 0 < T ∧ 0 ≤ B ∧ ∃ N : ℕ,
      ∃ E : ∀ k : ℕ, ControlledBlowupCylinder S (G.subsequence (k + N)) W T B 1,
      ∃ F : ℕ → RicciFlow 3 Y (Icc (-T) 0),
        (∀ (k : ℕ) (x : Y), (G.embedding (k + N) x.val).val ∈
          S.baseBall (G.subsequence (k + N)) W) ∧
        (∀ (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-T) 0) (x : Y)
            (v w : TangentSpace (𝓡 3) x),
          ((F k).metric s).inner x v w = (E k).embedding.pullbackInner s hs
            (G.embedding (k + N) x.val).val
            (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => (G.embedding (k + N) y.val).val) x v)
            (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => (G.embedding (k + N) y.val).val) x w)) ∧
        (∀ (k : ℕ) (x : Y) (v w : TangentSpace (𝓡 3) x),
          ((F k).metric 0).inner x v w =
            (terminalComponentMetric S (G.subsequence (k + N))).inner
              (G.embedding (k + N) x.val)
              (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => G.embedding (k + N) y.val) x v)
              (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => G.embedding (k + N) y.val) x w)) ∧
        ∀ m : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ k s, s ∈ Icc (-(T / 2)) 0 → ∀ x : Y,
          ((F k).connection s).curvatureDerivativeNorm m x ≤ D := by
  classical
  intro Y
  obtain ⟨R, hR, himage⟩ := G.exists_eventually_compact_image_ball hcomplete
    (G.exhaustion_compactClosure j)
  let W := R + 1
  have hW : 0 < W := by dsimp [W]; linarith
  have hRW : R < W := by dsimp [W]; linarith
  obtain ⟨T, hT, B, hB, hcyl⟩ :=
    exists_radius_dependent_controlled_cylinders hC H hbound W hW
  have hGamma : 0 < (R + W) / 2 := by positivity
  have htail :=
    (G.subsequence_strictMono.tendsto_atTop.eventually (hcyl 1 zero_lt_one)).and
      ((G.subsequence_strictMono.tendsto_atTop.eventually
        (H.balls_compact ((R + W) / 2) hGamma)).and
        (himage.and (eventually_ge_atTop j)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hNk (k : ℕ) := hN (k + N) (by omega)
  let C (k : ℕ) := (S.flow (G.subsequence (k + N))).slice
    (S.base (G.subsequence (k + N))).1
  let g (k : ℕ) : RiemannianMetric 3 (C k).carrier :=
    M13.scaleSmoothMetric ((S.flow (G.subsequence (k + N))).metric
      (S.base (G.subsequence (k + N))).1)
      (S.scale (G.subsequence (k + N))) (S.base_scalar_pos (G.subsequence (k + N)))
  have hballs (k : ℕ) (r : ℝ) :
      (g k).ball (S.base (G.subsequence (k + N))).2 r =
        S.baseBall (G.subsequence (k + N)) r :=
    scaled_terminal_ball_eq_baseBall S (G.subsequence (k + N)) r
  let U (k : ℕ) : TopologicalSpace.Opens (C k).carrier :=
    ⟨S.baseBall (G.subsequence (k + N)) W,
      baseBall_isOpen S (G.subsequence (k + N)) W⟩
  let E (k : ℕ) : ControlledBlowupCylinder S (G.subsequence (k + N)) W T B 1 :=
    Classical.choice (hNk k).1
  have hsource (k : ℕ) := exists_controlled_ordinary_source (E k) hW hT
  let Fsrc (k : ℕ) : RicciFlow 3 (U k) (Icc (-T) 0) :=
    Classical.choose (hsource k)
  have hsrc (k : ℕ) := (Classical.choose_spec (hsource k)).1
  have hterminal (k : ℕ) := (Classical.choose_spec (hsource k)).2.1
  let f (k : ℕ) : Y → (terminalComponentCarrier S (G.subsequence (k + N))).carrier :=
    fun x => G.embedding (k + N) x.val
  have hf (k : ℕ) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (f k) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) Y x).comp (𝓡 3)
      (terminalComponentCarrier S (G.subsequence (k + N))).carrier
      (G.embedding_smooth (k + N)
        ⟨x.val, G.exhaustion_monotone (hNk k).2.2.2 x.property⟩)
  have hpoint (k : ℕ) (x : Y) :
      (f k x).val ∈ (g k).ball (S.base (G.subsequence (k + N))).2 R := by
    have hcomponent := mem_image_of_mem Subtype.val
      ((hNk k).2.2.1 (mem_image_of_mem _ (subset_closure x.property)))
    rw [terminalComponentMetric_image_ball] at hcomponent
    exact (hballs k R).symm ▸ hcomponent
  have hU (k : ℕ) : (U k : Set (C k).carrier) =
      (g k).ball (S.base (G.subsequence (k + N))).2 W :=
    (hballs k W).symm
  have himageU (k : ℕ) (x : Y) : (f k x).val ∈ U k := by
    change (f k x).val ∈ (U k : Set (C k).carrier)
    rw [hU k]
    exact (hpoint k x).trans_le (ENNReal.ofReal_le_ofReal hRW.le)
  let e (k : ℕ) : Y → U k := fun x => ⟨(f k x).val, himageU k x⟩
  have hpull (k : ℕ) := exists_component_source_pullback (C k)
    (S.base (G.subsequence (k + N))).2 (g k) (U k) (Fsrc k)
      (hterminal k) (f k) (hf k) (himageU k)
  let F (k : ℕ) : RicciFlow 3 Y (Icc (-T) 0) := Classical.choose (hpull k)
  have hF (k : ℕ) := Classical.choose_spec (hpull k)
  let J : SpacetimeInterval := {
    domain := Icc (-T) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩,
      by linarith⟩ }
  have hcurv (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-T) 0) (x : U k) :
      ((Fsrc k).connection s).curvatureTensorNorm x ≤ B := by
    rw [(Cylinder.curvature_of_ordinaryFlow (J := J) (E k).embedding
      (Fsrc k) (hsrc k) s hs x).2]
    apply (div_le_iff₀ (S.base_scalar_pos (G.subsequence (k + N)))).mpr
    exact (le_abs_self _).trans ((E k).curvature_bound s hs x.val x.property)
  refine ⟨W, T, B, hW, hT, hB, N, E, F, himageU, ?_, ?_, ?_⟩
  · intro k s hs x v w
    rw [(hF k).1 s x v w, hsrc k s hs]
    have he : ContMDiff (𝓡 3) (𝓡 3) ∞ (e k) := by
      apply (ContMDiff.subtypeVal_comp_iff (U k) (e k)).mp
      change ContMDiff (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ f k)
      exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3)
        (Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3))
          (S.base (G.subsequence (k + N))).2)).contMDiff.comp (hf k).contMDiff
    have hderiv := mfderiv_comp x
      (contMDiff_subtype_val (n := ∞) (e k x) |>.mdifferentiableAt (by simp))
      ((he x).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (fun y : Y => (G.embedding (k + N) y.val).val) x =
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U k → (C k).carrier) (e k x)).comp
        (mfderiv (𝓡 3) (𝓡 3) (e k) x) at hderiv
    rw [hderiv]
    rfl
  · exact fun k x v w => (hF k).2.1 x v w
  · intro m
    obtain ⟨D, hD, hShi⟩ := exists_uniform_curvatureDerivativeNorm_bound_on_terminal_buffer
      hC.local_derivative_estimates 3 m B T R W hT hR hRW
    refine ⟨D, hD, ?_⟩
    intro k s hs x
    rw [(hF k).2.2 m s x]
    apply hShi (C k).carrier (g k) (S.base (G.subsequence (k + N))).2 (U k)
      (hU k) (Fsrc k) (hterminal k) (hcurv k) ?_ s hs (e k x) (hpoint k x)
    rw [hballs]
    exact (hNk k).2.1

end PoincareConjecture.M30
