import PoincareConjecture.Proofs.M28.Generalized.IndexedSourceFlows
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceBounds
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckNormalCovers
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCompactCore













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28





structure CounterexampleSourceGeometry {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E) where
  curvatureBound : ℝ
  curvatureBound_pos : 0 < curvatureBound
  derivativeBound : ℕ → ℝ
  derivativeBound_pos : ∀ m, 0 < derivativeBound m
  curvature_bound : ∀ (v : ℕ → ℝ)
    (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper)
    (k : ℕ) (s : ℝ), s ∈ Icc (-(1 / 2 : ℝ)) 0 →
    ∀ x : H.selectedSourceOpen v hv k,
      ((H.normalizedSourceFlow v hv k).connection s).curvatureTensorNorm x ≤ curvatureBound
  derivative_bound : ∀ (v : ℕ → ℝ)
    (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper)
    (m k : ℕ), ∀ q ∈ ((H.normalizedSourceFlow v hv k).metric 0).ball
      (H.normalizedSourceNeck v hv k).center (epsilon⁻¹ / 16),
      ((H.normalizedSourceFlow v hv k).connection 0).curvatureDerivativeNorm m q ≤
        derivativeBound m
  compact_core : ∀ (v : ℕ → ℝ)
    (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper) (k : ℕ),
    let N := H.normalizedSourceNeck v hv k
    ∃ hle : N.epsilon ≤ 64 * N.epsilon, ∃ hhalf : 64 * N.epsilon < 1 / 2,
      let N' := N.restrict_m28 (64 * N.epsilon) hle hhalf
      IsCompact (closure N'.carrier) ∧ closure N'.carrier ⊆
        ((H.normalizedSourceFlow v hv k).metric 0).ball N.center (epsilon⁻¹ / 16)
  normal_covers : ∀ r : ℝ, 0 < r → r < epsilon⁻¹ / 16 →
    ∃ R ρ : ℝ, ∃ n : ℕ, 0 < ρ ∧ 2 * ρ < R ∧
      R < (epsilon⁻¹ / 16 - r) / 8 ∧ R < 1 / 8 ∧
      ∀ (v : ℕ → ℝ)
        (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper) (k : ℕ),
        Nonempty (NormalChartCover (fun _ => (H.normalizedSourceFlow v hv k).metric 0)
          (H.normalizedSourceNeck v hv k).center (-1) 1 r R ρ (1 / 4) (9 / 4) n)





theorem exists_counterexample_source_family_accuracy
    (P : RicciFlowCurvatureTheory.{u}) (T : RepairedNeckCapTopologyTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 256 : ℝ) ∧
      ∀ (epsilon C A : ℝ), 0 < epsilon → epsilon ≤ epsilon₀ → 0 < C →
        ∀ E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1),
          ∃ H : CounterexampleNeckFamily E, Nonempty (CounterexampleSourceGeometry H) := by
  classical
  obtain ⟨eSelect, heSelect, _, hselect⟩ := exists_counterexample_neck_family_accuracy P T
  obtain ⟨eBounds, heBounds, _, K, hK, hbounds⟩ :=
    exists_strongNeck_source_bounds_accuracy P.local_derivative_estimates
  obtain ⟨eCover, heCover, _, hcover⟩ := exists_strongNeck_source_normal_covers_accuracy.{u}
  obtain ⟨eCore, heCore, heCoreSmall, hcore⟩ := exists_source_neck_compact_core_accuracy.{u}
  let epsilon₀ := min eSelect (min eBounds (min eCover eCore))
  have hSelect : epsilon₀ ≤ eSelect := min_le_left _ _
  have hBounds : epsilon₀ ≤ eBounds := (min_le_right _ _).trans (min_le_left _ _)
  have hCover : epsilon₀ ≤ eCover :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hCore : epsilon₀ ≤ eCore :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨epsilon₀, lt_min heSelect (lt_min heBounds (lt_min heCover heCore)),
    hCore.trans heCoreSmall, ?_⟩
  intro epsilon C A hepsilon hsmall hC E
  obtain ⟨H⟩ := hselect epsilon C A hepsilon (hsmall.trans hSelect) hC E
  obtain ⟨B, hB, hgeometry⟩ := hbounds epsilon hepsilon (hsmall.trans hBounds)
  refine ⟨H, ⟨{
    curvatureBound := K
    curvatureBound_pos := hK
    derivativeBound := B
    derivativeBound_pos := hB
    curvature_bound := ?_
    derivative_bound := ?_
    compact_core := ?_
    normal_covers := ?_ }⟩⟩
  · intro v hv k s hs x
    exact (hgeometry (E (k + H.shift)).flow (E (k + H.shift)).time
      (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)).1 s hs x
  · intro v hv m k q hq
    exact (hgeometry (E (k + H.shift)).flow (E (k + H.shift)).time
      (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)).2 m q hq
  · intro v hv k
    have h := hcore (H.selectedSourceOpen v hv k)
      ((H.normalizedSourceFlow v hv k).metric 0) (H.normalizedSourceNeck v hv k)
      (hsmall.trans hCore)
    simpa only [CounterexampleNeckFamily.normalizedSourceNeck,
      GeneralizedStrongNeck.rescaled_half_source_neck_scale,
      GeneralizedStrongNeck.rescaled_half_source_neck_epsilon, one_mul] using h
  · intro r hr hrb
    obtain ⟨R, ρ, n, hρ, hρR, hRmargin, hRsmall, hc⟩ :=
      hcover epsilon hepsilon (hsmall.trans hCover) r hr hrb
    refine ⟨R, ρ, n, hρ, hρR, hRmargin, hRsmall, ?_⟩
    intro v hv k
    exact hc (E (k + H.shift)).flow (E (k + H.shift)).time
      (H.selectedOriginalNeck v hv k) (H.rawSourceRescaling v hv k)

end PoincareConjecture.M28
