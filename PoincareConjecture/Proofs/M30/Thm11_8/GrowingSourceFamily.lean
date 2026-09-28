import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ControlledSource
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.IntrinsicBalls
import PoincareConjecture.Proofs.M30.Generalized.OrdinaryCurvature
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30





theorem exists_growing_ordinary_source_family
    (S : GeneralizedBlowupSequence.{u}) (rho v T B : ℝ)
    (hrho : 0 < rho) (hT : 0 < T) (hcompact : BlowupBaseBallsCompact S) :
    let W : ℕ → ℝ := fun k => (k : ℝ) + rho + 2
    let hW : ∀ k, 0 < W k := fun k => by dsimp [W]; positivity
    let C : ℕ → GeneralizedSliceCarrier.{u} := fun j => (S.flow j).slice (S.base j).1
    let gbar : ∀ j : ℕ, RiemannianMetric 3 (C j).carrier := fun j =>
      M13.scaleSmoothMetric ((S.flow j).metric (S.base j).1)
        (S.scale j) (S.base_scalar_pos j)
    let U : ∀ j : ℕ, ℕ → TopologicalSpace.Opens (C j).carrier := fun j k =>
      ⟨S.baseBall j (W k), baseBall_isOpen S j (W k)⟩
    let p : ∀ j k : ℕ, U j k := fun j k =>
      ⟨(S.base j).2, (baseBall_pointed_connected S j (hW k)).1⟩
    (∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta → ∀ᶠ j : ℕ in atTop,
      Nonempty (ControlledBlowupCylinder S j A T B eta)) →
    (∀ᶠ j : ℕ in atTop, ENNReal.ofReal v ≤
      calibratedMetricVolume (gbar j) ((gbar j).ball (S.base j).2 rho)) →
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ E : ∀ k : ℕ,
        ControlledBlowupCylinder S (sigma k) (W k) T B (1 / ((k : ℝ) + 1)),
      ∃ G : ∀ k : ℕ, RicciFlow 3 (U (sigma k) k) (Icc (-T) 0),
        (∀ (k : ℕ) (s : ℝ) (hs : s ∈ Icc (-T) 0) (x : U (sigma k) k)
            (z w : TangentSpace (𝓡 3) x),
          ((G k).metric s).inner x z w = (E k).embedding.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x z)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x w)) ∧
        (∀ (k : ℕ) (x : U (sigma k) k) (z w : TangentSpace (𝓡 3) x),
          ((G k).metric 0).inner x z w = (gbar (sigma k)).inner x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x z)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U (sigma k) k → (C (sigma k)).carrier) x w)) ∧
        (∀ (k : ℕ) (s : ℝ), s ∈ Icc (-T) 0 → ∀ x : U (sigma k) k,
          ((G k).connection s).curvatureTensorNorm x ≤ B) ∧
        (∀ k : ℕ, ((G k).connection 0).scalarCurvature (p (sigma k) k) = 1) ∧
        (∀ k : ℕ, ENNReal.ofReal v ≤
          ((G k).metric 0).volumeMeasure (((G k).metric 0).ball (p (sigma k) k) rho)) ∧
        ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
          IsCompact (closure (((G k).metric 0).ball (p (sigma k) k) A)) := by
  classical
  dsimp only
  let W (k : ℕ) : ℝ := (k : ℝ) + rho + 2
  let L (k : ℕ) : ℝ := (k : ℝ) + rho + 1
  let Gamma (k : ℕ) : ℝ := (L k + W k) / 2
  let C (j : ℕ) := (S.flow j).slice (S.base j).1
  let gbar (j : ℕ) : RiemannianMetric 3 (C j).carrier :=
    M13.scaleSmoothMetric ((S.flow j).metric (S.base j).1)
      (S.scale j) (S.base_scalar_pos j)
  have hW (k : ℕ) : 0 < W k := by dsimp [W]; positivity
  have hrhoW (k : ℕ) : rho < W k := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    dsimp [W]
    linarith
  have hGamma (k : ℕ) : 0 < Gamma k := by dsimp [Gamma, L, W]; positivity
  have hLGamma (k : ℕ) : L k < Gamma k := by dsimp [Gamma, W, L]; linarith
  have hLW (k : ℕ) : L k < W k := by dsimp [W, L]; linarith
  intro hcyl hvolume
  have hrows (k : ℕ) : ∀ᶠ j : ℕ in atTop,
      Nonempty (ControlledBlowupCylinder S j (W k) T B (1 / ((k : ℝ) + 1))) ∧
        IsCompact (closure (S.baseBall j (Gamma k))) ∧
          ENNReal.ofReal v ≤
            calibratedMetricVolume (gbar j) ((gbar j).ball (S.base j).2 rho) :=
    (hcyl (W k) (hW k) (1 / ((k : ℝ) + 1)) (by positivity)).and
      ((hcompact (Gamma k) (hGamma k)).and hvolume)
  obtain ⟨sigma, hsigma, hselect⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually hrows
  have hrow (k : ℕ) := hselect k k le_rfl
  let U (k : ℕ) : TopologicalSpace.Opens (C (sigma k)).carrier :=
    ⟨S.baseBall (sigma k) (W k), baseBall_isOpen S (sigma k) (W k)⟩
  let p (k : ℕ) : U k :=
    ⟨(S.base (sigma k)).2, (baseBall_pointed_connected S (sigma k) (hW k)).1⟩
  let E (k : ℕ) :
      ControlledBlowupCylinder S (sigma k) (W k) T B (1 / ((k : ℝ) + 1)) :=
    Classical.choice (hrow k).1
  have hsource (k : ℕ) := exists_controlled_ordinary_source (E k) (hW k) hT
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
    apply (div_le_iff₀ (S.base_scalar_pos (sigma k))).mpr
    exact (le_abs_self _).trans ((E k).curvature_bound s hs x.val x.property)
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
      IsCompact (closure (((G k).metric 0).ball (p k) (L k))) :=
    intrinsic_isCompact_closure_ball (gbar (sigma k)) (U k) ((G k).metric 0)
      (hmetric k) (p k) (hcompactAmbient k) (hclosureSubset k)
  refine ⟨sigma, hsigma, E, G, hG, hmetric, hcurv, ?_, ?_, ?_⟩
  · intro k
    have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
    rw [(Cylinder.curvature_of_ordinaryFlow (J := J) (E k).embedding (G k)
      (hG k) 0 hzero (p k)).1, (E k).zero_identity hzero (p k).val (p k).property]
    exact div_self (S.base_scalar_pos (sigma k)).ne'
  · intro k
    have hballSubset :
        (gbar (sigma k)).ball (S.base (sigma k)).2 rho ⊆ U k := by
      rw [hU k]
      exact fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal (hrhoW k).le)
    have hvolumeEq := intrinsic_calibratedMetricVolume_ball
      (gbar (sigma k)) (U k) ((G k).metric 0) (hmetric k) (p k) hballSubset
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
