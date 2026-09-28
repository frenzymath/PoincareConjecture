import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ControlledSource
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.IntrinsicBalls
import PoincareConjecture.Proofs.M30.Generalized.OrdinaryCurvature
import PoincareConjecture.Proofs.M30.Generalized.OrdinaryNegativeDefect
import PoincareConjecture.Proofs.M30.Generalized.WorldlineUniqueness
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal
import Mathlib.Order.Filter.Finite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem exists_growing_time_ordinary_source_family
    (S : GeneralizedBlowupSequence.{u}) (rho v : ℝ) (T B : ℕ → ℝ)
    (hrho : 0 < rho) (hT : ∀ j, 0 < T j) (hTmono : Monotone T)
    (hcompact : BlowupBaseBallsCompact S) :
    let W : ℕ → ℝ := fun k => (k : ℝ) + rho + 2
    let eta : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    let hW : ∀ k, 0 < W k := fun k => by dsimp [W]; positivity
    let C : ℕ → GeneralizedSliceCarrier.{u} := fun n => (S.flow n).slice (S.base n).1
    let gbar : ∀ n : ℕ, RiemannianMetric 3 (C n).carrier := fun n =>
      M13.scaleSmoothMetric ((S.flow n).metric (S.base n).1)
        (S.scale n) (S.base_scalar_pos n)
    let U : ∀ n : ℕ, ℕ → TopologicalSpace.Opens (C n).carrier := fun n k =>
      ⟨S.baseBall n (W k), baseBall_isOpen S n (W k)⟩
    let p : ∀ n k : ℕ, U n k := fun n k =>
      ⟨(S.base n).2, (baseBall_pointed_connected S n (hW k)).1⟩
    (∀ j : ℕ, ∀ A : ℝ, 0 < A → ∀ error : ℝ, 0 < error → ∀ᶠ n : ℕ in atTop,
      Nonempty (ControlledBlowupCylinder S n A (T j) (B j) error)) →
    (∀ᶠ n : ℕ in atTop, ENNReal.ofReal v ≤
      calibratedMetricVolume (gbar n) ((gbar n).ball (S.base n).2 rho)) →
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ E : ∀ k : ℕ,
        ControlledBlowupCylinder S (sigma k) (W k) (T k) (B k) (eta k),
      ∃ F : ∀ k : ℕ, RicciFlow 3 (U (sigma k) k) (Icc (-(T k)) 0),
        (∀ (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-(T k)) 0) (x : U (sigma k) k)
            (z w : TangentSpace (𝓡 3) x),
          ((F k).metric s).inner x z w = (E k).embedding.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x z)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x w)) ∧
        (∀ (k : ℕ) (x : U (sigma k) k) (z w : TangentSpace (𝓡 3) x),
          ((F k).metric 0).inner x z w = (gbar (sigma k)).inner x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x z)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x w)) ∧
        (∀ j k : ℕ, j ≤ k → ∀ s : ℝ, s ∈ Icc (-(T j)) 0 →
          ∀ x : U (sigma k) k, ((F k).connection s).curvatureTensorNorm x ≤ B j) ∧
        (∀ (k : ℕ) (s : ℝ), s ∈ Icc (-(T k)) 0 → ∀ x : U (sigma k) k,
          0 ≤ ((F k).connection s).negativeCurvaturePart x ∧
            ((F k).connection s).negativeCurvaturePart x ≤ eta k) ∧
        (∀ k : ℕ, ((F k).connection 0).scalarCurvature (p (sigma k) k) = 1) ∧
        (∀ k : ℕ, ENNReal.ofReal v ≤
          ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p (sigma k) k) rho)) ∧
        ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
          IsCompact (closure (((F k).metric 0).ball (p (sigma k) k) A)) := by
  classical
  dsimp only
  let W (k : ℕ) : ℝ := (k : ℝ) + rho + 2
  let eta (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let L (k : ℕ) : ℝ := (k : ℝ) + rho + 1
  let Gamma (k : ℕ) : ℝ := (L k + W k) / 2
  let C (n : ℕ) := (S.flow n).slice (S.base n).1
  let gbar (n : ℕ) : RiemannianMetric 3 (C n).carrier :=
    M13.scaleSmoothMetric ((S.flow n).metric (S.base n).1)
      (S.scale n) (S.base_scalar_pos n)
  have hW (k : ℕ) : 0 < W k := by dsimp [W]; positivity
  have heta (k : ℕ) : 0 < eta k := by dsimp [eta]; positivity
  have hrhoW (k : ℕ) : rho < W k := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    dsimp [W]
    linarith
  have hGamma (k : ℕ) : 0 < Gamma k := by dsimp [Gamma, L, W]; positivity
  have hLGamma (k : ℕ) : L k < Gamma k := by dsimp [Gamma, W, L]; linarith
  have hLW (k : ℕ) : L k < W k := by dsimp [W, L]; linarith
  intro hcyl hvolume
  have hfinite (k : ℕ) : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range (k + 1),
      Nonempty (ControlledBlowupCylinder S n (W k) (T j) (B j) (eta k)) := by
    apply (Filter.eventually_all_finset (Finset.range (k + 1))).2
    intro j _hj
    exact hcyl j (W k) (hW k) (eta k) (heta k)
  have hrows (k : ℕ) : ∀ᶠ n : ℕ in atTop,
      (∀ j : ℕ, j ≤ k →
        Nonempty (ControlledBlowupCylinder S n (W k) (T j) (B j) (eta k))) ∧
        IsCompact (closure (S.baseBall n (Gamma k))) ∧
          ENNReal.ofReal v ≤
            calibratedMetricVolume (gbar n) ((gbar n).ball (S.base n).2 rho) := by
    filter_upwards [hfinite k, hcompact (Gamma k) (hGamma k), hvolume] with n hn hball hv
    refine ⟨?_, hball, hv⟩
    intro j hj
    exact hn j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  obtain ⟨sigma, hsigma, hselect⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually hrows
  have hrow (k : ℕ) := hselect k k le_rfl
  let U (k : ℕ) : TopologicalSpace.Opens (C (sigma k)).carrier :=
    ⟨S.baseBall (sigma k) (W k), baseBall_isOpen S (sigma k) (W k)⟩
  let p (k : ℕ) : U k :=
    ⟨(S.base (sigma k)).2, (baseBall_pointed_connected S (sigma k) (hW k)).1⟩
  let A (k j : ℕ) (hjk : j ≤ k) :
      ControlledBlowupCylinder S (sigma k) (W k) (T j) (B j) (eta k) :=
    Classical.choice ((hrow k).1 j hjk)
  let E (k : ℕ) :
      ControlledBlowupCylinder S (sigma k) (W k) (T k) (B k) (eta k) := A k k le_rfl
  have hsource (k : ℕ) := exists_controlled_ordinary_source (E k) (hW k) (hT k)
  let F (k : ℕ) : RicciFlow 3 (U k) (Icc (-(T k)) 0) := Classical.choose (hsource k)
  have hF (k : ℕ) := (Classical.choose_spec (hsource k)).1
  have hmetric (k : ℕ) := (Classical.choose_spec (hsource k)).2.1
  let J (k : ℕ) : SpacetimeInterval := {
    domain := Icc (-(T k)) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-(T k), ⟨le_rfl, by linarith [hT k]⟩,
      0, ⟨by linarith [hT k], le_rfl⟩, by linarith [hT k]⟩ }
  have hzero (k : ℕ) : (0 : ℝ) ∈ Icc (-(T k)) 0 := ⟨by linarith [hT k], le_rfl⟩
  have hcurv (j k : ℕ) (hjk : j ≤ k) (s : ℝ) (hs : s ∈ Icc (-(T j)) 0)
      (x : U k) : ((F k).connection s).curvatureTensorNorm x ≤ B j := by
    have hsk : s ∈ Icc (-(T k)) 0 :=
      ⟨(neg_le_neg (hTmono hjk)).trans hs.1, hs.2⟩
    have hmeet : (E k).embedding.pointMap 0 (hzero k) x.val =
        (A k j hjk).embedding.pointMap 0 (hzero j) x.val :=
      ((E k).zero_identity (hzero k) x.val x.property).trans
        ((A k j hjk).zero_identity (hzero j) x.val x.property).symm
    have hpoint := Cylinder.pointMap_eq_on_overlap (E k).embedding (A k j hjk).embedding
      ordConnected_Icc ordConnected_Icc x.property x.property (hzero k) (hzero j) hmeet
      s hsk hs
    rw [(Cylinder.curvature_of_ordinaryFlow (J := J k) (E k).embedding (F k)
      (hF k) s hsk x).2, hpoint]
    apply (div_le_iff₀ (S.base_scalar_pos (sigma k))).mpr
    exact (le_abs_self _).trans ((A k j hjk).curvature_bound s hs x.val x.property)
  have hdefect (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-(T k)) 0) (x : U k) :
      0 ≤ ((F k).connection s).negativeCurvaturePart x ∧
        ((F k).connection s).negativeCurvaturePart x ≤ eta k := by
    constructor
    · exact le_max_right _ _
    · rw [Cylinder.negativeCurvaturePart_of_ordinaryFlow (J := J k) (E k).embedding
        (F k) (hF k) s hs x]
      apply (div_le_iff₀ (S.base_scalar_pos (sigma k))).mpr
      exact (E k).negative_curvature_bound s hs x.val x.property
  have hballs (k : ℕ) (r : ℝ) :
      (gbar (sigma k)).ball (S.base (sigma k)).2 r = S.baseBall (sigma k) r :=
    scaled_terminal_ball_eq_baseBall S (sigma k) r
  have hU (k : ℕ) : (U k : Set (C (sigma k)).carrier) =
      (gbar (sigma k)).ball (S.base (sigma k)).2 (W k) := (hballs k (W k)).symm
  have hcompactAmbient (k : ℕ) :
      IsCompact (closure ((gbar (sigma k)).ball (S.base (sigma k)).2 (L k))) := by
    have hbig : IsCompact
        (closure ((gbar (sigma k)).ball (S.base (sigma k)).2 (Gamma k))) := by
      rw [hballs]
      exact (hrow k).2.1
    exact hbig.of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal (hLGamma k).le))
  have hclosureSubset (k : ℕ) :
      closure ((gbar (sigma k)).ball (S.base (sigma k)).2 (L k)) ⊆ U k := by
    let : LocallyCompactSpace (C (sigma k)).carrier :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) (C (sigma k)).carrier
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (C (sigma k)).carrier → Type _) :=
      ⟨(gbar (sigma k)).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : (C (sigma k)).carrier → Type _) :=
      ⟨⟨(gbar (sigma k)).inner, (gbar (sigma k)).toContinuousRiemannianMetric.continuous,
        fun _ _ _ => rfl⟩⟩
    let : EMetricSpace (C (sigma k)).carrier :=
      EMetricSpace.ofRiemannianMetric (𝓡 3) (C (sigma k)).carrier
    have hclosed : IsClosed {y : (C (sigma k)).carrier |
        edist (S.base (sigma k)).2 y ≤ ENNReal.ofReal (L k)} :=
      isClosed_le (continuous_const.edist continuous_id) continuous_const
    have hsub : (gbar (sigma k)).ball (S.base (sigma k)).2 (L k) ⊆
        {y : (C (sigma k)).carrier | edist (S.base (sigma k)).2 y ≤ ENNReal.ofReal (L k)} := by
      intro y hy
      change edist (S.base (sigma k)).2 y < ENNReal.ofReal (L k) at hy
      exact hy.le
    intro y hy
    rw [hU k]
    exact (closure_minimal hsub hclosed hy).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (hW k)).mpr (hLW k))
  have hcompactSource (k : ℕ) :
      IsCompact (closure (((F k).metric 0).ball (p k) (L k))) :=
    intrinsic_isCompact_closure_ball (gbar (sigma k)) (U k) ((F k).metric 0)
      (hmetric k) (p k) (hcompactAmbient k) (hclosureSubset k)
  refine ⟨sigma, hsigma, E, F, hF, hmetric, hcurv, hdefect, ?_, ?_, ?_⟩
  · intro k
    rw [(Cylinder.curvature_of_ordinaryFlow (J := J k) (E k).embedding (F k)
      (hF k) 0 (hzero k) (p k)).1,
      (E k).zero_identity (hzero k) (p k).val (p k).property]
    exact div_self (S.base_scalar_pos (sigma k)).ne'
  · intro k
    have hballSubset :
        (gbar (sigma k)).ball (S.base (sigma k)).2 rho ⊆ U k := by
      rw [hU k]
      exact fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal (hrhoW k).le)
    have hvolumeEq := intrinsic_calibratedMetricVolume_ball
      (gbar (sigma k)) (U k) ((F k).metric 0) (hmetric k) (p k) hballSubset
    rw [← calibratedMetricVolume_eq_volumeMeasure, hvolumeEq]
    exact (hrow k).2.2
  · intro A _hA
    obtain ⟨N, hN⟩ := exists_nat_ge A
    filter_upwards [eventually_ge_atTop N] with k hk
    have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hAL : A ≤ L k := by dsimp [L]; linarith
    exact (hcompactSource k).of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hAL))

end PoincareConjecture.M30
