import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ControlledSource
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.IntrinsicBalls
import PoincareConjecture.Proofs.M30.Generalized.OrdinaryCurvature
import PoincareConjecture.Proofs.M30.Thm3_28.TerminalBuffer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem exists_retained_ordinary_source_family
    (hShi : LocalCurvatureDerivativeEstimates.{u}) (S : GeneralizedBlowupSequence.{u})
    (A rho v T B : ℝ) (hA : 0 < A) (hrho : 0 < rho) (hT : 0 < T) :
    let L := 3 * A + 2 * rho
    let W := L + 1
    let hW : 0 < W := add_pos
      (add_pos (mul_pos (zero_lt_three : (0 : ℝ) < 3) hA)
        (mul_pos (zero_lt_two : (0 : ℝ) < 2) hrho)) zero_lt_one
    let Gamma := (L + W) / 2
    let C : ℕ → GeneralizedSliceCarrier.{u} := fun j => (S.flow j).slice (S.base j).1
    let gbar : ∀ j : ℕ, RiemannianMetric 3 (C j).carrier := fun j =>
      M13.scaleSmoothMetric ((S.flow j).metric (S.base j).1)
        (S.scale j) (S.base_scalar_pos j)
    let U : ∀ j : ℕ, TopologicalSpace.Opens (C j).carrier := fun j =>
      ⟨S.baseBall j W, baseBall_isOpen S j W⟩
    let p : ∀ j : ℕ, U j := fun j =>
      ⟨(S.base j).2, (baseBall_pointed_connected S j hW).1⟩
    (∀ᶠ j : ℕ in atTop, Nonempty (ControlledBlowupCylinder S j W T B 1)) →
    (∀ᶠ j : ℕ in atTop, IsCompact (closure (S.baseBall j Gamma))) →
    (∀ᶠ j : ℕ in atTop, ENNReal.ofReal v ≤
      calibratedMetricVolume (gbar j) ((gbar j).ball (S.base j).2 rho)) →
    ∃ N : ℕ,
      ∃ E : ∀ k : ℕ, ControlledBlowupCylinder S (k + N) W T B 1,
      ∃ G : ∀ k : ℕ, RicciFlow 3 (U (k + N)) (Icc (-T) 0),
        (∀ (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-T) 0) (x : U (k + N))
            (z w : TangentSpace (𝓡 3) x),
          ((G k).metric s).inner x z w = (E k).embedding.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (k + N) → (C (k + N)).carrier) x z)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (k + N) → (C (k + N)).carrier) x w)) ∧
        (∀ (k : ℕ) (x : U (k + N)) (z w : TangentSpace (𝓡 3) x),
          ((G k).metric 0).inner x z w = (gbar (k + N)).inner x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (k + N) → (C (k + N)).carrier) x z)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (k + N) → (C (k + N)).carrier) x w)) ∧
        (∀ (k : ℕ) (s : ℝ), s ∈ Icc (-T) 0 → ∀ x : U (k + N),
          ((G k).connection s).curvatureTensorNorm x ≤ B) ∧
        (∀ k : ℕ, IsCompact (closure (((G k).metric 0).ball (p (k + N)) L))) ∧
        (∀ k : ℕ, ENNReal.ofReal v ≤
          ((G k).metric 0).volumeMeasure (((G k).metric 0).ball (p (k + N)) rho)) ∧
        ∀ m : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ (k : ℕ) (s : ℝ), s ∈ Icc (-(T / 2)) 0 →
          ∀ x : U (k + N), x ∈ ((G k).metric 0).ball (p (k + N)) A →
            ((G k).connection s).curvatureDerivativeNorm m x ≤ D := by
  classical
  dsimp only
  let L := 3 * A + 2 * rho
  let W := L + 1
  let Gamma := (L + W) / 2
  let C (j : ℕ) := (S.flow j).slice (S.base j).1
  let gbar (j : ℕ) : RiemannianMetric 3 (C j).carrier :=
    M13.scaleSmoothMetric ((S.flow j).metric (S.base j).1)
      (S.scale j) (S.base_scalar_pos j)
  have hW : 0 < W := by dsimp [W, L]; linarith
  have hAW : A < W := by dsimp [W, L]; linarith
  have hrhoW : rho < W := by dsimp [W, L]; linarith
  have hLGamma : L < Gamma := by dsimp [Gamma, W]; linarith
  have hLW : L < W := by dsimp [W]; linarith
  have hmidGamma : (A + W) / 2 < Gamma := by dsimp [Gamma, W, L]; linarith
  intro hcyl hcompact hvolume
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcyl.and (hcompact.and hvolume))
  have htail (k : ℕ) := hN (k + N) (by omega)
  let U (k : ℕ) : TopologicalSpace.Opens (C (k + N)).carrier :=
    ⟨S.baseBall (k + N) W, baseBall_isOpen S (k + N) W⟩
  let p (k : ℕ) : U k :=
    ⟨(S.base (k + N)).2, (baseBall_pointed_connected S (k + N) hW).1⟩
  let E (k : ℕ) : ControlledBlowupCylinder S (k + N) W T B 1 :=
    Classical.choice (htail k).1
  have hsource (k : ℕ) := exists_controlled_ordinary_source (E k) hW hT
  let G (k : ℕ) : RicciFlow 3 (U k) (Icc (-T) 0) := Classical.choose (hsource k)
  have hG (k : ℕ) := (Classical.choose_spec (hsource k)).1
  have hmetric (k : ℕ) := (Classical.choose_spec (hsource k)).2.1
  let J : SpacetimeInterval := {
    domain := Icc (-T) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩,
      by linarith⟩ }
  have hcurv (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-T) 0) (x : U k) :
      ((G k).connection s).curvatureTensorNorm x ≤ B := by
    rw [(Cylinder.curvature_of_ordinaryFlow (J := J) (E k).embedding (G k)
      (hG k) s hs x).2]
    apply (div_le_iff₀ (S.base_scalar_pos (k + N))).mpr
    exact (le_abs_self _).trans ((E k).curvature_bound s hs x.val x.property)
  have hballs (k : ℕ) (r : ℝ) :
      (gbar (k + N)).ball (S.base (k + N)).2 r = S.baseBall (k + N) r :=
    scaled_terminal_ball_eq_baseBall S (k + N) r
  have hU (k : ℕ) : (U k : Set (C (k + N)).carrier) =
      (gbar (k + N)).ball (S.base (k + N)).2 W := (hballs k W).symm
  have hballSubset (k : ℕ) {r : ℝ} (hrW : r ≤ W) :
      (gbar (k + N)).ball (S.base (k + N)).2 r ⊆ U k := by
    rw [hU k]
    exact fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hrW)
  have hcompactAmbient (k : ℕ) {r : ℝ} (hrGamma : r ≤ Gamma) :
      IsCompact (closure ((gbar (k + N)).ball (S.base (k + N)).2 r)) := by
    have hbig : IsCompact
        (closure ((gbar (k + N)).ball (S.base (k + N)).2 Gamma)) := by
      rw [hballs]
      exact (htail k).2.1
    exact hbig.of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hrGamma))
  have hclosureSubset (k : ℕ) {r : ℝ} (hrW : r < W) :
      closure ((gbar (k + N)).ball (S.base (k + N)).2 r) ⊆ U k := by
    let : LocallyCompactSpace (C (k + N)).carrier :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) (C (k + N)).carrier
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (C (k + N)).carrier → Type _) :=
      ⟨(gbar (k + N)).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : (C (k + N)).carrier → Type _) :=
      ⟨⟨(gbar (k + N)).inner, (gbar (k + N)).toContinuousRiemannianMetric.continuous,
        fun _ _ _ => rfl⟩⟩
    let : EMetricSpace (C (k + N)).carrier :=
      EMetricSpace.ofRiemannianMetric (𝓡 3) (C (k + N)).carrier
    have hclosed : IsClosed {y : (C (k + N)).carrier |
        edist (S.base (k + N)).2 y ≤ ENNReal.ofReal r} :=
      isClosed_le (continuous_const.edist continuous_id) continuous_const
    have hsub : (gbar (k + N)).ball (S.base (k + N)).2 r ⊆
        {y : (C (k + N)).carrier | edist (S.base (k + N)).2 y ≤ ENNReal.ofReal r} := by
      intro y hy
      change edist (S.base (k + N)).2 y < ENNReal.ofReal r at hy
      exact hy.le
    intro y hy
    rw [hU k]
    exact (closure_minimal hsub hclosed hy).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hW).mpr hrW)
  refine ⟨N, E, G, hG, hmetric, hcurv, ?_, ?_, ?_⟩
  · intro k
    exact intrinsic_isCompact_closure_ball (gbar (k + N)) (U k) ((G k).metric 0)
      (hmetric k) (p k) (hcompactAmbient k hLGamma.le) (hclosureSubset k hLW)
  · intro k
    have hvolumeEq := intrinsic_calibratedMetricVolume_ball
      (gbar (k + N)) (U k) ((G k).metric 0) (hmetric k) (p k)
      (hballSubset k hrhoW.le)
    rw [← calibratedMetricVolume_eq_volumeMeasure, hvolumeEq]
    exact (htail k).2.2
  · intro m
    obtain ⟨D, hD, hbound⟩ :=
      exists_uniform_curvatureDerivativeNorm_bound_on_terminal_buffer
        hShi 3 m B T A W hT hA hAW
    refine ⟨D, hD, ?_⟩
    intro k s hs x hx
    apply hbound (C (k + N)).carrier (gbar (k + N)) (S.base (k + N)).2 (U k)
      (hU k) (G k) (hmetric k) (hcurv k) (hcompactAmbient k hmidGamma.le) s hs x
    exact (((G k).metric 0).edist_map_le_of_metric_pullback
      (gbar (k + N)) contMDiff_subtype_val (hmetric k) (p k) x).trans_lt hx

end PoincareConjecture.M30
