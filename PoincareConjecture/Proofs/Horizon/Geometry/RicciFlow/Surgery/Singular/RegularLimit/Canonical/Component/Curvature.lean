import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.CurvatureConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.LowerBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace SingularCComponent

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {C : ℝ}

theorem curvatureTensor_lower_bound_by_scalar (N : SingularCComponent g D C)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier)
    (v w : TangentSpace (𝓡 3) y) :
    C⁻¹ * D.scalarCurvature x * (g.inner y v v * g.inner y w w - (g.inner y v w) ^ 2) ≤
      D.curvatureTensor y v w v w := by
  obtain ⟨B, hB⟩ := N.compact.bddAbove_image D.continuous_scalarCurvature.continuousOn
  have hb : BddAbove (range (fun z : N.carrier => D.scalarCurvature z.1)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hB ⟨z.1, z.2, rfl⟩
  have hsup : D.scalarCurvature x ≤ scalarCurvatureSupOn g D N.carrier :=
    le_csSup hb ⟨⟨x, hx⟩, rfl⟩
  apply D.curvatureTensor_diagonal_lower_bound_of_orthonormal
  intro a b ha hb hab
  exact (mul_le_mul_of_nonneg_left hsup (inv_pos.mpr N.constant_pos).le).trans
    (N.sectional_lower y hy a b ⟨ha, hb, hab⟩).le

end SingularCComponent

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminal_curvatureTensor_lower_bound_of_frequently_cComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    {y z : H.regularRegion P04} (hy : y ∈ connectedComponent x)
    (hz : z ∈ connectedComponent x) (v w : TangentSpace (𝓡 3) y) :
    H.constant⁻¹ * (H.terminalConnection P04).scalarCurvature z *
        ((H.terminalMetric P04).inner y v v * (H.terminalMetric P04).inner y w w -
          ((H.terminalMetric P04).inner y v w) ^ 2) ≤
      (H.terminalConnection P04).curvatureTensor y v w v w := by
  have hm (a b : TangentSpace (𝓡 3) y) :
      Tendsto (fun t => (H.reference.flow.metric t).inner (y : M) a b) (𝓝[<] T)
        (𝓝 ((H.terminalMetric P04).inner y a b)) :=
    H.tendsto_terminalMetricBilinear_apply P04 y.property a b
  have hleft := ((H.tendsto_terminal_scalarCurvature P04 z).const_mul H.constant⁻¹).mul
    (((hm v v).mul (hm w w)).sub ((hm v w).pow 2))
  apply le_of_tendsto_of_tendsto_of_frequently hleft
    (H.tendsto_terminal_curvatureTensor P04 y v w v w)
  apply hfreq.mono
  rintro t ⟨ht, N, hxN⟩
  let N' := H.reference.referenceCComponent t ht N
  have hcarrier : N'.carrier = connectedComponent (x : M) :=
    H.reference.referenceCComponent_carrier t ht N hxN
  have hym : (y : M) ∈ N'.carrier := by
    rw [hcarrier]
    exact continuous_subtype_val.image_connectedComponent_subset x ⟨y, hy, rfl⟩
  have hzm : (z : M) ∈ N'.carrier := by
    rw [hcarrier]
    exact continuous_subtype_val.image_connectedComponent_subset x ⟨z, hz, rfl⟩
  exact N'.curvatureTensor_lower_bound_by_scalar hzm hym v w

theorem terminal_sectional_lower_bound_of_frequently_cComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    {y z : H.regularRegion P04} (hy : y ∈ connectedComponent x)
    (hz : z ∈ connectedComponent x) (v w : TangentSpace (𝓡 3) y)
    (hvw : LeviCivitaData.IsOrthonormalPair (H.terminalMetric P04) y v w) :
    H.constant⁻¹ * (H.terminalConnection P04).scalarCurvature z ≤
      (H.terminalConnection P04).sectionalCurvature y v w := by
  have h := H.terminal_curvatureTensor_lower_bound_of_frequently_cComponent P04 x hfreq hy hz v w
  simpa only [LeviCivitaData.sectionalCurvature, hvw.1, hvw.2.1, hvw.2.2,
    mul_one, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, div_one] using h

theorem terminal_strict_sectional_bounds_of_frequently_cComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    ∀ y ∈ connectedComponent x, ∀ v w : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (H.terminalMetric P04) y v w →
      0 < (H.terminalConnection P04).sectionalCurvature y v w ∧
        (2 * H.constant)⁻¹ * scalarCurvatureSupOn (H.terminalMetric P04)
          (H.terminalConnection P04) (connectedComponent x) <
            (H.terminalConnection P04).sectionalCurvature y v w := by
  intro y hy v w hvw
  have hsec_pos := (mul_pos (inv_pos.mpr H.constant_pos) hpos).trans_le
    (H.terminal_sectional_lower_bound_of_frequently_cComponent P04 x hfreq hy
      mem_connectedComponent v w hvw)
  have hsup : scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04)
      (connectedComponent x) ≤ H.constant * (H.terminalConnection P04).sectionalCurvature y v w := by
    unfold scalarCurvatureSupOn
    apply csSup_le (s := range (fun z : connectedComponent x =>
      (H.terminalConnection P04).scalarCurvature z.1)) ⟨_, ⟨⟨x, mem_connectedComponent⟩, rfl⟩⟩
    rintro _ ⟨z, rfl⟩
    have hz := H.terminal_sectional_lower_bound_of_frequently_cComponent P04 x hfreq hy
      z.property v w hvw
    have hm := mul_le_mul_of_nonneg_left hz H.constant_pos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ H.constant_pos.ne', one_mul] using hm
  have hfactor : 0 ≤ (2 * H.constant)⁻¹ := by positivity [H.constant_pos]
  have hscaled := mul_le_mul_of_nonneg_left hsup hfactor
  have heq : (2 * H.constant)⁻¹ *
      (H.constant * (H.terminalConnection P04).sectionalCurvature y v w) =
        (H.terminalConnection P04).sectionalCurvature y v w / 2 := by
    field_simp [H.constant_pos.ne']
  rw [heq] at hscaled
  exact ⟨hsec_pos, hscaled.trans_lt (by linarith)⟩

theorem terminal_scalar_lower_bound_of_frequently_cComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    {y : H.regularRegion P04} (hy : y ∈ connectedComponent x) :
    6 * (H.constant⁻¹ * (H.terminalConnection P04).scalarCurvature x) ≤
      (H.terminalConnection P04).scalarCurvature y := by
  apply normalization_scalarCurvature_lower_bound
  intro v w hvw
  have h := H.terminal_curvatureTensor_lower_bound_of_frequently_cComponent P04 x hfreq
    hy mem_connectedComponent v w
  simpa only [hvw.1, hvw.2.1, hvw.2.2, mul_one,
    zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using h

end SingularTimeAssumptions

end PoincareConjecture
