import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Volume.ScaleRange
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.LateControl



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_eventually_captured_cap_neck_scalar_bounds
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ C : CapCertificate (F.metric t), C.cap_constant ≤ H.constant →
          C.connection = F.connection t →
          H.reference.inverse t ht '' C.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ C.core →
          ∀ N : EpsilonNeck (F.metric t), N.carrier ⊆ C.carrier →
            l ≤ N.connection.scalarCurvature N.center ∧
              N.connection.scalarCurvature N.center ≤ u := by
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  have hbase : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  obtain ⟨u, hu, hupper⟩ := H.exists_eventually_captured_cap_scalar_upper P04 hA
  refine ⟨m / H.constant, u, div_pos hm H.constant_pos, hu, ?_⟩
  filter_upwards [hbase, hupper] with t hbase hupper
  intro ht C hconstant hconnection hcapture hcore N hNC
  have hcenter := hNC (N.central_sphere_subset N.center_on_central_sphere)
  have hscalar := N.connection.scalarCurvature_eq C.connection N.center
  have hpos := C.scalar_pos N.center hcenter
  have hratio := C.scalar_lt_constant_mul hcenter (C.core_subset_carrier hcore)
  have hbaseeq : C.connection.scalarCurvature (H.reference.forward t ht x₀) =
      H.reference.scalar t x₀ := by
    rw [hconnection, H.reference.scalar_pullback]
    rfl
  rw [hbaseeq] at hratio
  rw [hscalar]
  refine ⟨?_, (hupper ht C hconnection hcapture).1 N.center hcenter⟩
  apply (div_le_iff₀ H.constant_pos).mpr
  have hmul := mul_le_mul_of_nonneg_right hconstant hpos.le
  nlinarith

end PoincareConjecture.SingularTimeAssumptions
