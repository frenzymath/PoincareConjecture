import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.PointedCompactnessInput
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FiniteSourcePullback
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import Mathlib.Topology.Instances.ENNReal.Lemmas













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold





theorem exists_expanding_reference_source_family
    {T0 : ℝ≥0∞} (T B : ℕ → ℝ)
    (hT : ∀ k, 0 < T k ∧ ENNReal.ofReal (T k) < T0)
    (hTmono : Monotone T)
    (hcofinal : ∀ s : ℝ, ENNReal.ofReal s < T0 →
      ∀ᶠ k in atTop, s < T k)
    {rho v : ℝ} (hrho : 0 < rho) (hv : 0 < v)
    (N : ℕ → Type u)
    [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    [∀ k, T3Space (N k)] [∀ k, SecondCountableTopology (N k)]
    [∀ k, ConnectedSpace (N k)]
    [∀ k, MeasurableSpace (N k)] [∀ k, BorelSpace (N k)]
    (O : ∀ k, RicciFlow 3 (N k) (Icc (-(T k)) 0))
    (p : ∀ k, N k)
    (hcurv : ∀ j k, j ≤ k → ∀ s ∈ Icc (-(T j)) 0, ∀ x : N k,
      ((O k).connection s).curvatureTensorNorm x ≤ B j)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal v ≤
      ((O k).metric 0).volumeMeasure (((O k).metric 0).ball (p k) rho))
    (hcompact : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      IsCompact (closure (((O k).metric 0).ball (p k) A))) :
    let theta : ℝ := min 1 (T 0 / 2)
    let r : ℝ := theta / 2
    let J : ℕ → Set ℝ := fun k => Icc (r - T k) r
    let W : Set ℝ := {t | t < r ∧ ENNReal.ofReal (r - t) < T0}
    (0 < theta ∧ theta ≤ 1 ∧ theta < T 0) ∧
      IsOpen W ∧ W.OrdConnected ∧ Ioo (-theta / 2) (theta / 2) ⊆ W ∧
      ∃ Href : PointedRicciFlowCompactnessHypotheses 3 (-theta / 2) (theta / 2),
        ∃ e : ∀ k, (Href.sequence.carrier k).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N k,
          (∀ k, e k (Href.sequence.flow k).base = p k) ∧
          let Fseq : ∀ k,
              RicciFlow 3 (Href.sequence.carrier k).carrier (J k) := fun k =>
            ((O k).pullbackDiffeomorph (e k)).translate (-r)
              (by
                rintro _ ⟨t, ht, rfl⟩
                exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
              ordConnected_Icc
              (by
                refine ⟨r - T k, ⟨le_rfl, ?_⟩, r, ⟨?_, le_rfl⟩, ?_⟩
                all_goals linarith [(hT k).1])
          (∀ k, (Fseq k).metric = (Href.sequence.flow k).flow.metric) ∧
            ∀ a b : ℝ, Icc a b ⊆ W →
              ∃ j : ℕ, 0 ≤ B j ∧ ∀ k, j ≤ k →
                Icc a b ⊆ J k ∧
                  ∀ t ∈ Icc a b, ∀ x : (Href.sequence.carrier k).carrier,
                    ((Fseq k).connection t).curvatureTensorNorm x ≤ B j := by
  classical
  dsimp only
  let theta : ℝ := min 1 (T 0 / 2)
  let r : ℝ := theta / 2
  let W : Set ℝ := {t | t < r ∧ ENNReal.ofReal (r - t) < T0}
  have htheta : 0 < theta := lt_min zero_lt_one (half_pos (hT 0).1)
  have htheta1 : theta ≤ 1 := min_le_left _ _
  have hthetaT : theta < T 0 :=
    (min_le_right _ _).trans_lt (half_lt_self (hT 0).1)
  have hthetak (k : ℕ) : theta ≤ T k :=
    hthetaT.le.trans (hTmono (Nat.zero_le k))
  have hshort (k : ℕ) : Icc (-theta) 0 ⊆ Icc (-(T k)) 0 := by
    intro t ht
    exact ⟨(neg_le_neg (hthetak k)).trans ht.1, ht.2⟩
  have hshortne : (Icc (-theta) 0).Nontrivial := by
    refine ⟨-theta, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, ?_⟩
    linarith
  let Oshort (k : ℕ) : RicciFlow 3 (N k) (Icc (-theta) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow
      (O k) (hshort k) ordConnected_Icc hshortne
  have hcurvShort (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-theta) 0) (x : N k) :
      ((Oshort k).connection t).curvatureTensorNorm x ≤ B 0 :=
    hcurv 0 k (Nat.zero_le k) t
      ⟨(neg_le_neg hthetaT.le).trans ht.1, ht.2⟩ x
  obtain ⟨Href, hHref⟩ :=
    exists_pointedCompactnessHypotheses_of_finite_source_family
      htheta hrho hv N Oshort p hcurvShort hvolume hcompact
  choose e heBase heMetric using hHref
  have hmetricPull (k : ℕ) (t : ℝ) :
      ((O k).pullbackDiffeomorph (e k)).metric t =
        (Href.sequence.flow k).flow.metric (t + theta / 2) :=
    pullback_source_metric_eq_shifted_pointed_metric Href.sequence Oshort e heMetric k t
  have hWopen : IsOpen W := by
    change IsOpen (Iio r ∩ (fun t : ℝ => ENNReal.ofReal (r - t)) ⁻¹' Iio T0)
    exact isOpen_Iio.inter (isOpen_Iio.preimage
      (ENNReal.continuous_ofReal.comp (continuous_const.sub continuous_id)))
  have hWord : W.OrdConnected := by
    refine ⟨?_⟩
    intro x hx y hy z hz
    exact ⟨hz.2.trans_lt hy.1,
      (ENNReal.ofReal_le_ofReal (sub_le_sub_left hz.1 r)).trans_lt hx.2⟩
  have hwindow : Ioo (-theta / 2) (theta / 2) ⊆ W := by
    intro t ht
    refine ⟨ht.2, ?_⟩
    have hrt : r - t ≤ T 0 := by dsimp [r]; linarith [ht.1]
    exact (ENNReal.ofReal_le_ofReal hrt).trans_lt (hT 0).2
  have hB (j : ℕ) : 0 ≤ B j := by
    have hnonneg : 0 ≤ ((O j).connection 0).curvatureTensorNorm (p j) :=
      Real.sqrt_nonneg _
    exact hnonneg.trans (hcurv j j le_rfl 0 ⟨by linarith [(hT j).1], le_rfl⟩ (p j))
  refine ⟨⟨htheta, htheta1, hthetaT⟩, hWopen, hWord, hwindow, Href, e, heBase, ?_, ?_⟩
  · intro k
    funext t
    change ((O k).pullbackDiffeomorph (e k)).metric (t + -r) =
      (Href.sequence.flow k).flow.metric t
    rw [hmetricPull]
    congr 1
    dsimp [r]
    ring
  · intro a b hab
    by_cases hab' : a ≤ b
    · have ha : a ∈ W := hab ⟨le_rfl, hab'⟩
      have hb : b < r := (hab ⟨hab', le_rfl⟩).1
      obtain ⟨j, hj⟩ := (hcofinal (r - a) ha.2).exists
      refine ⟨j, hB j, ?_⟩
      intro k hjk
      constructor
      · intro t ht
        change t ∈ Icc (r - T k) r
        exact ⟨by linarith [hTmono hjk, ht.1], ht.2.trans hb.le⟩
      · intro t ht x
        change (((O k).pullbackDiffeomorph (e k)).connection
          (t + -r)).curvatureTensorNorm x ≤ B j
        rw [RicciFlow.pullbackDiffeomorph_curvatureTensorNorm]
        exact hcurv j k hjk (t + -r)
          ⟨by linarith [ht.1], by linarith [ht.2]⟩ (e k x)
    · refine ⟨0, hB 0, fun k _ => ⟨?_, ?_⟩⟩
      · intro t ht
        exact (hab' (ht.1.trans ht.2)).elim
      · intro t ht x
        exact (hab' (ht.1.trans ht.2)).elim

end PoincareConjecture.M30
