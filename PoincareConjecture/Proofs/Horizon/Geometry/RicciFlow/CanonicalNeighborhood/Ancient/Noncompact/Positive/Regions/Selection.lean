import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Enclosure
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive


theorem uniform_curvature_scale_separation_of_services
    (P : NoncompactKappaServices.{u}) {a : ℝ} (ha : 0 ≤ a) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p q : M),
        ¬ IsCompact (univ : Set M) →
        L * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ) <
          ((K.flow.metric 0).edist p q).toReal →
        a < Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist p q).toReal := by
  obtain ⟨C, hC, hbound⟩ := nonround_uniform_core_scalar_upper_of_services P
    (show 0 < a + 1 by linarith)
  have hCpos : 0 < C := zero_lt_one.trans hC
  refine ⟨(a + 1) * Real.sqrt C, mul_pos (by linarith) (Real.sqrt_pos.mpr hCpos), ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p q hnoncompact hd
  have hpos (x : M) : 0 < (K.flow.connection 0).scalarCurvature x := by
    obtain ⟨N⟩ := P.normalization M K x 0 le_rfl
    exact N.scale_eq ▸ N.scale_pos
  have hp := hpos p
  have hq := hpos q
  have hpsqrt := Real.sqrt_pos.mpr hp
  have hqsqrt := Real.sqrt_pos.mpr hq
  have hpower (x : M) : (K.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ) =
      (Real.sqrt ((K.flow.connection 0).scalarCurvature x))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg (hpos x).le, ← Real.sqrt_eq_rpow]
  rw [hpower, ← div_eq_mul_inv] at hd
  have hd' := (div_lt_iff₀ hpsqrt).mp hd
  by_contra hn
  have hn := le_of_not_gt hn
  have hmem : p ∈ (K.flow.metric 0).ball q
      ((a + 1) * (K.flow.connection 0).scalarCurvature q ^ (-1 / 2 : ℝ)) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top q p)).mpr
    rw [hpower, ← div_eq_mul_inv]
    apply (lt_div_iff₀ hqsqrt).mpr
    let := RiemannianMetric.toMetricSpace (K.flow.metric 0)
    have hcomm : (K.flow.metric 0).edist q p = (K.flow.metric 0).edist p q := edist_comm q p
    rw [hcomm]
    nlinarith
  have hscalar := hbound K q (K.not_isRound_of_noncompact hnoncompact) p hmem
  have hroot := Real.sqrt_lt_sqrt hp.le hscalar
  rw [Real.sqrt_mul hCpos.le] at hroot
  have hdist : 0 ≤ ((K.flow.metric 0).edist p q).toReal := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_right hroot.le hdist
  have hupper := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg C)
  nlinarith [Real.sqrt_pos.mpr hCpos]



theorem uniform_curvature_scale_separation
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {a : ℝ} (ha : 0 ≤ a) :
    ∃ L : ℝ, 0 < L ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p q : M),
        ¬ IsCompact (univ : Set M) →
        L * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ) <
          ((K.flow.metric 0).edist p q).toReal →
        a < Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
          ((K.flow.metric 0).edist p q).toReal := by
  exact uniform_curvature_scale_separation_of_services P.noncompactServices ha

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  [NoncompactSpace M]

omit [NoncompactSpace M] in


theorem exists_strong_neck_at_radius
    {K : AncientKappaSolution 3 M} {S : RiemannianMetric.PointSoulData (K.flow.metric 0)}
    {epsilon D D₁ : ℝ} (H : SoulCenteredCoreEstimate K S epsilon D D₁)
    {r : ℝ} (hr : 0 < r)
    (houtside : D * soulScalar K S.center ^ (-1 / 2 : ℝ) ≤ r) :
    ∃ N : StrongEvolvingNeck K 0 epsilon,
      ((K.flow.metric 0).edist S.center N.center).toReal = r := by
  classical
  let q : RiemannianMetric.UnitTwoSphere := Classical.choice inferInstance
  let x : M := S.radial.toHomeomorph (q, ⟨r, hr⟩)
  have hx : ((K.flow.metric 0).edist S.center x).toReal = r :=
    S.radial.distance_eq (q, ⟨r, hr⟩)
  obtain ⟨N, hN⟩ := H.strong_outside x (by
    intro hmem
    have hlt := (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top S.center x)).mp hmem
    rw [hx] at hlt
    exact (not_lt_of_ge houtside) hlt)
  exact ⟨N, hN ▸ hx⟩



theorem exists_enclosing_strong_neck_radius_of_services
    (P : NoncompactKappaServices.{u}) {D a : ℝ} (hD : 1 < D)
    (ha : 0 ≤ a) :
    ∃ R : ℝ, 4 * D ≤ R ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        [NoncompactSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D₁ : ℝ}, SoulCenteredCoreEstimate K S epsilon D D₁ →
        ∃ N : StrongEvolvingNeck K 0 epsilon,
          ((K.flow.metric 0).edist S.center N.center).toReal =
            R * soulScalar K S.center ^ (-1 / 2 : ℝ) ∧
          a * N.terminal_neck.scale <
            R * soulScalar K S.center ^ (-1 / 2 : ℝ) := by
  obtain ⟨L, hL, hseparation⟩ := uniform_curvature_scale_separation_of_services P ha
  let R := max (4 * D) (L + 1)
  have hDR : 4 * D ≤ R := le_max_left _ _
  have hLR : L < R := (by linarith : L < L + 1).trans_le (le_max_right _ _)
  refine ⟨R, hDR, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ K S epsilon D₁ H
  have hDpos : 0 < D := zero_lt_one.trans hD
  have hR : 0 < R := (mul_pos (by norm_num) hDpos).trans_le hDR
  have hscale : 0 < soulScalar K S.center ^ (-1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos H.soul_scalar_pos _
  obtain ⟨N, hcenter⟩ := exists_strong_neck_at_radius H (mul_pos hR hscale)
    (mul_le_mul_of_nonneg_right (by linarith : D ≤ R) hscale.le)
  refine ⟨N, hcenter, ?_⟩
  have hnoncompact : ¬ IsCompact (univ : Set M) := noncompact_univ M
  have hsep := hseparation K S.center N.center hnoncompact (by
    change L * soulScalar K S.center ^ (-1 / 2 : ℝ) < _
    rw [hcenter]
    exact mul_lt_mul_of_pos_right hLR hscale)
  have hqpos : 0 < (K.flow.connection 0).scalarCurvature N.center := by
    simpa only [N.terminal_connection, N.terminal_center] using
      N.terminal_neck.scalar_center_pos
  have hneckscale : N.terminal_neck.scale =
      (Real.sqrt ((K.flow.connection 0).scalarCurvature N.center))⁻¹ := by
    rw [N.terminal_neck.scale_eq_scalar, N.terminal_connection, N.terminal_center,
      show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg hqpos.le, ← Real.sqrt_eq_rpow]
  have hcancel : Real.sqrt ((K.flow.connection 0).scalarCurvature N.center) *
      N.terminal_neck.scale = 1 := by
    rw [hneckscale, mul_inv_cancel₀ (Real.sqrt_pos.mpr hqpos).ne']
  have h := mul_lt_mul_of_pos_right hsep N.terminal_neck.scale_pos
  rw [mul_right_comm (Real.sqrt ((K.flow.connection 0).scalarCurvature N.center))
    ((K.flow.metric 0).edist S.center N.center).toReal N.terminal_neck.scale,
    hcancel, one_mul, hcenter] at h
  exact h



theorem exists_enclosing_strong_neck_radius
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {D a : ℝ} (hD : 1 < D)
    (ha : 0 ≤ a) :
    ∃ R : ℝ, 4 * D ≤ R ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        [NoncompactSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D₁ : ℝ}, SoulCenteredCoreEstimate K S epsilon D D₁ →
        ∃ N : StrongEvolvingNeck K 0 epsilon,
          ((K.flow.metric 0).edist S.center N.center).toReal =
            R * soulScalar K S.center ^ (-1 / 2 : ℝ) ∧
          a * N.terminal_neck.scale <
            R * soulScalar K S.center ^ (-1 / 2 : ℝ) := by
  exact exists_enclosing_strong_neck_radius_of_services P.noncompactServices hD ha



theorem exists_enclosing_strong_neck_regions_of_services
    (P : NoncompactKappaServices.{u}) {D : ℝ} (hD : 1 < D) :
    ∃ R : ℝ, 4 * D ≤ R ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        [NoncompactSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D₁ : ℝ}, SoulCenteredCoreEstimate K S epsilon D D₁ →
        epsilon ≤ neckSeparationThreshold →
        ∃ (N : StrongEvolvingNeck K 0 epsilon) (A B : Set M),
          IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
          Disjoint A B ∧ A ∪ B = N.terminal_neck.central_sphereᶜ ∧
          frontier A = N.terminal_neck.central_sphere ∧
          frontier B = N.terminal_neck.central_sphere ∧
          IsCompact (closure A) ∧ S.center ∈ A ∧
          (K.flow.metric 0).ball S.center
            (D * soulScalar K S.center ^ (-1 / 2 : ℝ)) ⊆ A ∧
          closure A ⊆ (K.flow.metric 0).ball S.center
            ((2 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  obtain ⟨R, hDR, hneck⟩ := exists_enclosing_strong_neck_radius_of_services P hD
    (show 0 ≤ 8 * Real.pi by positivity)
  refine ⟨R, hDR, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ K S epsilon D₁ H hepsilon
  obtain ⟨N, hcenter, hscale⟩ := hneck K S H
  obtain ⟨A, B, hA, hB, hAc, hBc, hd, hu, hfA, hfB, hc, hp, hi, ho, _⟩ :=
    exists_quantitative_neck_regions S (K.complete 0 le_rfl) N.terminal_neck
      (N.terminal_epsilon.trans_le hepsilon)
  have hpos : 0 < soulScalar K S.center ^ (-1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos H.soul_scalar_pos _
  have hRpos : 0 < R := by linarith
  have hDscale : 4 * D * soulScalar K S.center ^ (-1 / 2 : ℝ) ≤
      R * soulScalar K S.center ^ (-1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hDR hpos.le
  have hcenter' : ((K.flow.metric 0).edist S.center N.terminal_neck.center).toReal =
      R * soulScalar K S.center ^ (-1 / 2 : ℝ) := N.terminal_center ▸ hcenter
  refine ⟨N, A, B, hA, hB, hAc, hBc, hd, hu, hfA, hfB, hc, hp, ?_, ?_⟩
  · intro x hx
    refine hi _ (mul_pos (by linarith : 0 < D) hpos) ?_ ?_
    · rw [hcenter']
      nlinarith
    · exact (ENNReal.lt_ofReal_iff_toReal_lt
        ((K.flow.metric 0).edist_ne_top S.center x)).mp hx
  · intro x hx
    have houter := ho hx
    change ((K.flow.metric 0).edist S.center x).toReal ≤ _ at houter
    rw [hcenter'] at houter
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top S.center x)).mpr
    have hRscale := mul_pos hRpos hpos
    nlinarith



theorem exists_enclosing_strong_neck_regions
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {D : ℝ} (hD : 1 < D) :
    ∃ R : ℝ, 4 * D ≤ R ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        [NoncompactSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {epsilon D₁ : ℝ}, SoulCenteredCoreEstimate K S epsilon D D₁ →
        epsilon ≤ neckSeparationThreshold →
        ∃ (N : StrongEvolvingNeck K 0 epsilon) (A B : Set M),
          IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
          Disjoint A B ∧ A ∪ B = N.terminal_neck.central_sphereᶜ ∧
          frontier A = N.terminal_neck.central_sphere ∧
          frontier B = N.terminal_neck.central_sphere ∧
          IsCompact (closure A) ∧ S.center ∈ A ∧
          (K.flow.metric 0).ball S.center
            (D * soulScalar K S.center ^ (-1 / 2 : ℝ)) ⊆ A ∧
          closure A ⊆ (K.flow.metric 0).ball S.center
            ((2 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ)) := by
  exact exists_enclosing_strong_neck_regions_of_services P.noncompactServices hD

end PoincareConjecture.NoncompactKappa.Positive
