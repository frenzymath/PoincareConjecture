import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CovariantComponentBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_UniformCoordinateJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ClosedTimeJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open M36

local notation "E" => StandardCapSpace
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

noncomputable local instance familyJetsCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance familyJetsCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 800000 in

theorem exists_uniform_singularMetricJetErrorSquared_bound
    (m : ℕ) {a : ℝ} (ha : 0 < a) (B0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
      (U : Set E), IsOpen U → ∀ (B : E → V), ContDiffOn ℝ ∞ B U →
      ∀ (x : E), x ∈ U → ∀ rho : ℝ, 0 ≤ rho →
      (∀ v : E, a * ‖v‖ ^ 2 ≤ g.inner x v v) →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ B0) →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (B - g.euclideanCoefficients) x‖ ≤ rho) →
      singularMetricJetErrorSquared g D (fun y v => B y (v 0) (v 1)) m x ≤
        C * rho ^ 2 := by
  classical
  obtain ⟨G, hG, hchrist⟩ := exists_uniform_comparisonChristoffel_bound m ha B0
  choose A hA hAbound using fun j : Fin (m + 1) =>
    exists_uniform_covariant_norm_bound 2 j ha hG
  let C := 1 + ∑ j : Fin (m + 1), (A j) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro g D U hU B hB x hx rho hrho hell hjets hbase
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  obtain ⟨F, hF, heq⟩ := exists_comparison_smooth_germ hU (hB.sub hg.contDiffOn) hx
  let T : CovariantTensorEvaluation 3 E 2 := fun y v => F y (v 0) (v 1)
  have hT : IsSmoothCovariantTensor T := comparison_bilinear_isSmooth hF
  have hcoeff (j : ℕ) (hj : j ≤ m) (b : Fin 2 → Fin 3) :
      ‖iteratedFDeriv ℝ j (comparisonTensorComponent T b) x‖ ≤ rho := by
    have h1 := norm_iteratedFDeriv_clm_apply_const (hF.contDiffAt (x := x))
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (c := e (b 0))
    have h2 := norm_iteratedFDeriv_clm_apply_const
      (((hF.contDiffAt (x := x)).clm_apply (contDiffAt_const (c := e (b 0)))))
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (c := e (b 1))
    simp only [(e).norm_eq_one, one_mul] at h1 h2
    apply (h2.trans h1).trans
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    exact hbase j hj
  have hTeq : ∀ᶠ y in nhds x,
      T y = (fun v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) := by
    filter_upwards [heq] with y hy
    funext v
    change F y (v 0) (v 1) = _
    rw [hy]
    rfl
  have hbound (j : Fin (m + 1)) :
      g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) j) x ≤ A j * rho := by
    have hn : g.tensorNorm (D.iteratedCovariantTensorDerivative T j) x =
        g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
          (fun y v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) j) x := by
      unfold RiemannianMetric.tensorNorm
      rw [(comparison_iteratedCovariantTensorDerivative_eventuallyEq D hTeq j).self_of_nhds]
    rw [← hn]
    exact hAbound j g D T hT x rho hrho hell
      (fun l hl => hchrist g x hell hjets l (by omega))
      (fun l hl b => hcoeff l (by omega) b)
  unfold singularMetricJetErrorSquared
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ ≤ ∑ j : Fin (m + 1), (A j * rho) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply (sq_le_sq₀ (by unfold RiemannianMetric.tensorNorm; positivity)
        (mul_nonneg (hA j).le hrho)).mpr
      exact hbound j
    _ = (∑ j : Fin (m + 1), (A j) ^ 2) * rho ^ 2 := by
      simp only [mul_pow, Finset.sum_mul]
    _ ≤ C * rho ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg rho)
      dsimp [C]
      linarith

theorem contDiffOn_euclideanCoefficients_within {J : Set ℝ}
    (F : RicciFlow 3 E J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => (F.metric p.1).euclideanCoefficients p.2)
      (J ×ˢ univ) := by
  have h := contDiffOn_pullbackCoefficients_within F isOpen_univ
    (contMDiff_id.contMDiffOn : ContMDiffOn (𝓡 3) (𝓡 3) ∞ id univ)
  apply h.congr
  intro p _
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change (F.metric p.1).inner p.2 v w =
    (F.metric p.1).inner p.2 (mfderiv (𝓡 3) (𝓡 3) id p.2 v)
      (mfderiv (𝓡 3) (𝓡 3) id p.2 w)
  rw [mfderiv_id]
  rfl

theorem continuousOn_standard_spatialJet {g0 : StandardInitialMetric}
    (S : PartialStandardCapFlow g0) (m : ℕ) :
    ContinuousOn (fun p : ℝ × E =>
      iteratedFDeriv ℝ m (S.flow.metric p.1).euclideanCoefficients p.2)
      (Ico 0 S.lifetime ×ˢ univ) :=
  (contDiffOn_spatialJet_within (contDiffOn_euclideanCoefficients_within S.flow)
    (uniqueDiffOn_Ico _ _) isOpen_univ m).continuousOn

theorem exists_standard_family_ellipticity_jet_bound {g0 : StandardInitialMetric}
    (S : PartialStandardCapFlow g0) {H : ℝ} (hH : H < S.lifetime)
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∃ B : ℝ, ∀ t ∈ Icc 0 H, ∀ x ∈ K,
      (∀ v : E, a * ‖v‖ ^ 2 ≤ (S.flow.metric t).inner x v v) ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (S.flow.metric t).euclideanCoefficients x‖ ≤ B) := by
  classical
  have hsub : Icc (0 : ℝ) H ×ˢ K ⊆ Ico 0 S.lifetime ×ˢ (univ : Set E) :=
    fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hH⟩, mem_univ _⟩
  have hcompact : IsCompact (Icc (0 : ℝ) H ×ˢ K) := isCompact_Icc.prod hK
  have hc := (contDiffOn_euclideanCoefficients_within S.flow).continuousOn.mono hsub
  obtain ⟨a, ha, hell⟩ := exists_uniform_bilinear_family_lower_bound hcompact hc
    (fun p _ v hv => (S.flow.metric p.1).pos p.2 v hv)
  choose B hB using fun j : Fin (m + 1) => hcompact.exists_bound_of_continuousOn
    ((continuousOn_standard_spatialJet S j).mono hsub)
  let B0 := ∑ j : Fin (m + 1), |B j|
  refine ⟨a, ha, B0, ?_⟩
  intro t ht x hx
  refine ⟨hell (t, x) ⟨ht, hx⟩, ?_⟩
  intro j hj
  have hbound := hB ⟨j, by omega⟩ (t, x) ⟨ht, hx⟩
  apply hbound.trans
  apply (le_abs_self _).trans
  dsimp only [B0]
  exact Finset.single_le_sum (fun q _ => abs_nonneg (B q))
    (Finset.mem_univ (⟨j, by omega⟩ : Fin (m + 1)))

theorem exists_standard_family_metricJetError_bound {g0 : StandardInitialMetric}
    (S : MaximalStandardCapFlow g0) {H : ℝ} (hH : H < S.base.lifetime)
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 H,
      ∀ (g : RiemannianMetric 3 E), g = S.metric t → ∀ (D : LeviCivitaData g),
      ∀ (U : Set E), IsOpen U →
      ∀ (B : E → V), ContDiffOn ℝ ∞ B U → ∀ x ∈ K, x ∈ U →
      ∀ rho : ℝ, 0 ≤ rho →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j (B - g.euclideanCoefficients) x‖ ≤ rho) →
      singularMetricJetErrorSquared g D
        (fun y v => B y (v 0) (v 1)) m x ≤ C * rho ^ 2 := by
  obtain ⟨a, ha, B0, hbackground⟩ :=
    exists_standard_family_ellipticity_jet_bound S.base hH hK (m + 1)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_singularMetricJetErrorSquared_bound m ha B0
  refine ⟨C, hC, ?_⟩
  intro t ht g hmetric D U hU B hB x hx hxU rho hrho hdiff
  subst g
  obtain ⟨hell, hjets⟩ := hbackground t ht x hx
  exact hbound (S.metric t) D U hU B hB x hxU rho hrho hell hjets hdiff

end PoincareConjecture.M44
