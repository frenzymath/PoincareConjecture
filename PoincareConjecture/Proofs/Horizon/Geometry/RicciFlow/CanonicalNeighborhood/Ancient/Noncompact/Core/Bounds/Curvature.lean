import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.NormalizedScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.RelativeScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem nonround_uniform_core_scalar_upper_of_services
    (P : NoncompactKappaServices.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          (K.flow.connection 0).scalarCurvature x <
            C * (K.flow.connection 0).scalarCurvature p := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨C, hC, hbound⟩ := noncompact_uniform_scalar_bound_of_normalized P hkappa hD
  refine ⟨C + 1, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround x hx
  let L : AncientKappaSolution 3 M := {
    K with
    kappa := kappa
    kappa_pos := hkappa
    noncollapsed := hnoncollapsed K hnonround
  }
  obtain ⟨N⟩ := P.normalization M L p 0 le_rfl
  have hscale : N.scale = (K.flow.connection 0).scalarCurvature p := N.scale_eq
  have hR : 0 < (K.flow.connection 0).scalarCurvature p := hscale ▸ N.scale_pos
  have htarget : AncientKappaNoncollapsed N.target.flow kappa := by
    have hk : N.target.kappa = kappa := N.target_kappa
    rw [← hk]
    exact N.target.noncollapsed
  have hpower : (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ) =
      (Real.sqrt ((K.flow.connection 0).scalarCurvature p))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow]
  have hxreal :=
    (ENNReal.lt_ofReal_iff_toReal_lt ((K.flow.metric 0).edist_ne_top p x)).mp hx
  rw [hpower] at hxreal
  have hsqrt : 0 < Real.sqrt ((K.flow.connection 0).scalarCurvature p) :=
    Real.sqrt_pos.mpr hR
  have hxnorm : x ∈ (N.target.flow.metric 0).ball p D := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      ((N.target.flow.metric 0).edist_ne_top p x)).mpr
    rw [N.toReal_edist_zero, hscale]
    change Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
      ((K.flow.metric 0).edist p x).toReal < D
    calc
      _ < Real.sqrt ((K.flow.connection 0).scalarCurvature p) *
          (D * (Real.sqrt ((K.flow.connection 0).scalarCurvature p))⁻¹) :=
        mul_lt_mul_of_pos_left hxreal hsqrt
      _ = D := by field_simp
  have hscalar := hbound N.target p htarget N.normalized_scalar x hxnorm
  rw [N.scalar_eq 0 le_rfl x, zero_div, zero_add] at hscalar
  have hresult : (K.flow.connection 0).scalarCurvature x ≤
      C * (K.flow.connection 0).scalarCurvature p := by
    simpa only [L, hscale] using (div_le_iff₀ N.scale_pos).mp hscalar
  calc
    _ ≤ C * (K.flow.connection 0).scalarCurvature p := hresult
    _ < (C + 1) * (K.flow.connection 0).scalarCurvature p := by nlinarith

theorem nonround_uniform_core_scalar_upper
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          (K.flow.connection 0).scalarCurvature x <
            C * (K.flow.connection 0).scalarCurvature p := by
  exact nonround_uniform_core_scalar_upper_of_services P.noncompactServices hD

theorem nonround_uniform_core_curvature_upper_of_services
    (P : NoncompactKappaServices.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          (K.flow.connection 0).curvatureTensorNorm x <
            C * (K.flow.connection 0).scalarCurvature p := by
  obtain ⟨C, hC, hbound⟩ := nonround_uniform_core_scalar_upper_of_services P hD
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround x hx
  exact (P.past_norm_le_scalar M K 0 0 le_rfl le_rfl x).trans_lt
    (hbound K p hnonround x hx)

theorem nonround_uniform_core_curvature_upper
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          (K.flow.connection 0).curvatureTensorNorm x <
            C * (K.flow.connection 0).scalarCurvature p := by
  exact nonround_uniform_core_curvature_upper_of_services P.noncompactServices hD

theorem nonround_uniform_core_sectional_upper_of_services
    (P : NoncompactKappaServices.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
        ∀ a b : TangentSpace (𝓡 3) x,
          |(K.flow.connection 0).sectionalCurvature x a b| <
            C * (K.flow.connection 0).scalarCurvature p := by
  obtain ⟨C, hC, hbound⟩ := nonround_uniform_core_curvature_upper_of_services P hD
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround x hx a b
  exact ((K.flow.connection 0).abs_sectionalCurvature_le_curvatureTensorNorm x a b).trans_lt
    (hbound K p hnonround x hx)

theorem nonround_uniform_core_sectional_upper
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 1 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ∀ x ∈ (K.flow.metric 0).ball p
          (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
        ∀ a b : TangentSpace (𝓡 3) x,
          |(K.flow.connection 0).sectionalCurvature x a b| <
            C * (K.flow.connection 0).scalarCurvature p := by
  exact nonround_uniform_core_sectional_upper_of_services P.noncompactServices hD

end PoincareConjecture
