import PoincareConjecture.Proofs.M35.CapGeometry.SelectedRadialFieldDomain
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCoordinateMetric
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCurvatureDerivativeRealization
import PoincareConjecture.Proofs.M35.CapGeometry.RetainedRadialFieldJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

noncomputable section

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "B" => V →L[ℝ] V →L[ℝ] ℝ

local instance selectedRadialBoundDualNormedGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  inferInstance
local instance selectedRadialBoundDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance selectedRadialBoundMetricNormedGroup : NormedAddCommGroup B := inferInstance
local instance selectedRadialBoundMetricNormedSpace : NormedSpace ℝ B := inferInstance



theorem blowupSequence_coordinate_radial_projected_jets_bounded
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (_hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible)
      (g : RiemannianMetric 3 V)
      (_hg : g.euclideanCoefficients = (L.limit.flow.metric 0).pullbackCoefficients coordinate)
      (K : Set V) (_hK : IsCompact K) (m : ℕ) (projection : V × ℝ →L[ℝ] W),
      ∃ C : ℝ, ∀ᶠ k in atTop,
        let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
        let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
        let G := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
        let f : V → StandardCapSpace := fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ (coordinate z)).val
        ∀ z ∈ K, ‖iteratedFDeriv ℝ m (fun y => projection
          (pullback ℝ f (radialUnitField G) y,
            axisWarpingSlope G ‖f y‖ / axisWarpingRadius G ‖f y‖)) z‖ ≤ C := by
  classical
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate hc hi g hg K hK m projection
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ k : 0 < Q k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G (k : ℕ) : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
  let DG (k : ℕ) : LeviCivitaData (G k) :=
    M13.scaleLeviCivitaData (E.flow.connection (t (L.subsequence k))) (Q k) (hQ k)
  let f (k : ℕ) (z : V) := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ (coordinate z)).val
  let Z k y := projection (pullback ℝ (f k) (radialUnitField (G k)) y,
    axisWarpingSlope (G k) ‖f k y‖ / axisWarpingRadius (G k) ‖f k y‖)
  change ∃ C : ℝ, ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (Z k) z‖ ≤ C
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (blowupSequence_coordinate_radial_domain P E t x ht hR hd L coordinate hc hi K hK)
  by_contra hbad
  simp only [eventually_atTop, not_exists, not_forall, not_le] at hbad
  have hchoose (n : ℕ) : ∃ k, max N n ≤ k ∧
      ∃ z ∈ K, (n : ℝ) < ‖iteratedFDeriv ℝ m (Z k) z‖ := by
    obtain ⟨k, hk, z, hz, hn⟩ := hbad n (max N n)
    exact ⟨k, hk, z, hz, hn⟩
  choose sigma hsigma zseq hzseq hlarge using hchoose
  have hsigmalim : Tendsto sigma atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_right N n).trans (hsigma n)) tendsto_id
  obtain ⟨p, _hpK, tau, htau, hplim⟩ := hK.tendsto_subseq hzseq
  let idx k := sigma (tau k)
  let pseq k := zseq (tau k)
  have hidx : Tendsto idx atTop atTop := hsigmalim.comp htau.tendsto_atTop
  have hpseq : Tendsto pseq atTop (𝓝 p) := hplim
  have hdomain (k : ℕ) := hN (idx k)
    ((le_max_left N (tau k)).trans (hsigma (tau k))) (pseq k) (hzseq (tau k))
  have hreal (k : ℕ) : ∃ gd : Σ g' : RiemannianMetric 3 V, LeviCivitaData g',
      (gd.1.euclideanCoefficients =ᶠ[𝓝 (pseq k)] (G (idx k)).pullbackCoefficients (f (idx k))) := by
    obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp (hdomain k).1
    obtain ⟨gk, Dk, hcoeff, _⟩ := exists_local_curvature_derivative_realization
      (G (idx k)) (DG (idx k)) (f (idx k)) hU hpU
      (fun y hy => (hUsub hy).1) (fun y hy => (hUsub hy).2.1)
    exact ⟨⟨gk, Dk⟩, hcoeff⟩
  choose gd hgd using hreal
  have hjets (r : ℕ) : Tendsto
      (fun k => iteratedFDeriv ℝ r (gd k).1.euclideanCoefficients (pseq k)) atTop
        (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients p)) := by
    apply blowupSequence_fixed_coordinate_metric_jets P E t x ht hR L
      coordinate hc pseq p hpseq idx hidx (fun k => (gd k).1) g ?_ ?_ r
    · exact Eventually.of_forall hgd
    · exact Eventually.of_forall fun y => congrFun hg y
  have hmetric : Tendsto (fun k => (gd k).1.euclideanCoefficients (pseq k)) atTop
      (𝓝 (g.euclideanCoefficients p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V B).continuous.tendsto _).comp (hjets 0)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  obtain ⟨a, ha, hlow⟩ := exists_uniform_bilinear_lower_bound
    («B» := fun _ : V => g.euclideanCoefficients p) (K := {0}) isCompact_singleton
    continuousOn_const (fun _ _ w hw => g.pos p w hw)
  have hell : ∀ᶠ k in atTop, ∀ w : V,
      (a / 2) * ‖w‖ ^ 2 ≤ (gd k).1.inner (pseq k) w w := by
    filter_upwards [Metric.tendsto_nhds.mp hmetric (a / 2) (half_pos ha)] with k hk w
    have he := (g.euclideanCoefficients p - (gd k).1.euclideanCoefficients (pseq k)).le_opNorm₂ w w
    change ‖g.inner p w w - (gd k).1.inner (pseq k) w w‖ ≤
      ‖g.euclideanCoefficients p - (gd k).1.euclideanCoefficients (pseq k)‖ * ‖w‖ * ‖w‖ at he
    have hnorm : ‖g.euclideanCoefficients p - (gd k).1.euclideanCoefficients (pseq k)‖ ≤ a / 2 := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using hk.le
    have hdiff : g.inner p w w - (gd k).1.inner (pseq k) w w ≤ (a / 2) * ‖w‖ ^ 2 := by
      calc
        _ ≤ |g.inner p w w - (gd k).1.inner (pseq k) w w| := le_abs_self _
        _ ≤ ‖g.euclideanCoefficients p - (gd k).1.euclideanCoefficients (pseq k)‖ * ‖w‖ ^ 2 := by
          simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using he
        _ ≤ _ := mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖w‖)
    have h := hlow 0 (mem_singleton _) w
    change a * ‖w‖ ^ 2 ≤ g.inner p w w at h
    nlinarith only [h, hdiff]
  obtain ⟨M, hM⟩ := eventually_atTop.mp hell
  let mu (k : ℕ) := k + M
  have hmu : StrictMono mu := fun i j hij => Nat.add_lt_add_right hij M
  have hrotation (k : ℕ) : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : V, (G (idx (mu k))).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G (idx (mu k))).inner x u v :=
    scaleSmoothMetric_rotation_invariant
      (E.rotation_invariant (t (L.subsequence (idx (mu k)))) (ht _)) _ _
  have hfg (k : ℕ) : ∀ᶠ y in 𝓝 (pseq (mu k)),
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f (idx (mu k))) y :=
    (hdomain (mu k)).1.mono fun _ hy => hy.1
  have hig (k : ℕ) : ∀ᶠ y in 𝓝 (pseq (mu k)),
      (mfderiv (𝓡 3) (𝓡 3) (f (idx (mu k))) y).IsInvertible :=
    (hdomain (mu k)).1.mono fun _ hy => hy.2.1
  have hmg (k : ℕ) : ∀ᶠ y in 𝓝 (pseq (mu k)), ∀ u v : V,
      (gd (mu k)).1.inner y u v = (G (idx (mu k))).inner (f (idx (mu k)) y)
        (mfderiv (𝓡 3) (𝓡 3) (f (idx (mu k))) y u)
        (mfderiv (𝓡 3) (𝓡 3) (f (idx (mu k))) y v) := by
    filter_upwards [hgd (mu k)] with y hy u v
    exact congrArg (fun b : B => b u v) hy
  have hzero (k : ℕ) : f (idx (mu k)) (pseq (mu k)) ≠ 0 :=
    (hdomain (mu k)).1.self_of_nhds.2.2
  have hj := retained_radial_field_shape_jets (fun k => (gd (mu k)).2)
    (fun k => DG (idx (mu k))) g.euclideanLeviCivitaData
    (fun k => f (idx (mu k))) (fun k => pseq (mu k)) p m hrotation hfg hig hmg hzero
    (half_pos ha) (fun k => hM (mu k) (Nat.le_add_left M k))
    ⟨1, fun k => (hdomain (mu k)).2⟩
    (fun r _ => (hjets r).comp hmu.tendsto_atTop)
  have hs (k : ℕ) : ContDiffAt ℝ ∞
      (fun y => (pullback ℝ (f (idx (mu k))) (radialUnitField (G (idx (mu k)))) y,
        axisWarpingSlope (G (idx (mu k))) ‖f (idx (mu k)) y‖ /
          axisWarpingRadius (G (idx (mu k))) ‖f (idx (mu k)) y‖)) (pseq (mu k)) := by
    have hf := contMDiffAt_iff_contDiffAt.mp (hfg k).self_of_nhds
    have hi' : (fderiv ℝ (f (idx (mu k))) (pseq (mu k))).IsInvertible := by
      simpa only [mfderiv_eq_fderiv] using (hig k).self_of_nhds
    exact (euclidean_radial_pullback_contDiffAt _ hf hi' (hzero k)).prodMk
      ((radial_shape_contDiffAt _ (hzero k)).comp _ hf)
  have hZ := hj.clm hs projection
  obtain ⟨C, hC⟩ := hZ m (Nat.le_succ m)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hupper : ‖iteratedFDeriv ℝ m (Z (idx (mu n))) (pseq (mu n))‖ ≤ C := hC n
  have hlower := hlarge (tau (mu n))
  have hnat : n ≤ tau (mu n) := (Nat.le_add_right n M).trans (htau.id_le (mu n))
  have hnat' : (n : ℝ) ≤ tau (mu n) := by exact_mod_cast hnat
  change (tau (mu n) : ℝ) <
    ‖iteratedFDeriv ℝ m (Z (idx (mu n))) (pseq (mu n))‖ at hlower
  exact (hn.trans_le hnat').not_ge (hlower.le.trans hupper)



theorem blowupSequence_coordinate_radial_jets_bounded
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (_hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible)
      (g : RiemannianMetric 3 V)
      (_hg : g.euclideanCoefficients = (L.limit.flow.metric 0).pullbackCoefficients coordinate)
      (K : Set V) (_hK : IsCompact K) (m : ℕ),
      ∃ C : ℝ, ∀ᶠ k in atTop,
        let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
        let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
        let G := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
        let f : V → StandardCapSpace := fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ (coordinate z)).val
        ∀ z ∈ K, ‖iteratedFDeriv ℝ m (pullback ℝ f (radialUnitField G)) z‖ ≤ C := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate hc hi g hg K hK m
  exact blowupSequence_coordinate_radial_projected_jets_bounded P E t x ht hR hd L
    coordinate hc hi g hg K hK m (ContinuousLinearMap.fst ℝ V ℝ)

end

end PoincareConjecture.M35.OrdinaryRealization
