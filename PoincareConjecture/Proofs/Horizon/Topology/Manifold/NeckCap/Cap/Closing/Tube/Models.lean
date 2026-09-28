import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Tube.CapAbsorption
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedModels.Transport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedModels.Euclidean
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedModels.MixedPair
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedModels.ProjectivePair
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ModelCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ProjectiveCoordinates

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.DoubleCappedTubeCertificate

theorem exists_closed_model_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (T : DoubleCappedTubeCertificate g),
        T.cap₁.epsilon = T.cap₂.epsilon →
        T.cap₁.epsilon = T.tube.epsilon → T.cap₁.epsilon ≤ ε₀ →
        (∃ x : M, T.carrier = connectedComponent x) →
        ∃ kind : ClosedComponentKind,
          Nonempty (ClosedComponentCertificate kind T.carrier) := by
  obtain ⟨ε₀, hε₀, hsmall, habsorb⟩ := CapTubeAttachment.exists_absorption_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall.trans (by norm_num), ?_⟩
  intro M _ _ _ _ _ _ _ g T _ _ hε hcomponent
  let U : Opens M := ⟨T.cap₁.carrier, T.cap₁.carrier_open⟩
  let V : Opens M := ⟨T.cap₂.carrier, T.cap₂.carrier_open⟩
  let W : Opens M := U ⊔ ⟨T.tube.carrier, T.tube.carrier_open⟩
  obtain ⟨_, _, E, _, _⟩ := habsorb T.first_attachment hε
  have hcompact : IsCompact ((W : Set M) ∪ V) := T.carrier_eq_union ▸ T.compact
  have hcomponent' : ∃ x : M, (W : Set M) ∪ V = connectedComponent x :=
    T.carrier_eq_union ▸ hcomponent
  rw [T.carrier_eq_union]
  change ∃ kind : ClosedComponentKind,
    Nonempty (ClosedComponentCertificate kind ((W : Set M) ∪ V))
  cases hC : T.cap₁.model_kind with
  | euclidean =>
    obtain ⟨a, has, hat, ha, hai⟩ := T.cap₁.exists_euclidean_coordinates hC
    obtain ⟨e, hes, het, he, hei⟩ :=
      ClosedModels.exists_euclidean_chart_of_open_diffeomorph U W E a has hat ha hai
    cases hD : T.cap₂.model_kind with
    | euclidean =>
      obtain ⟨f, hfs, hft, hf, hfi⟩ := T.cap₂.exists_euclidean_coordinates hD
      exact ⟨.threeSphere, ClosedModels.nonempty_euclidean_pair_certificate W V e f
        hes het hfs hft he hei hf hfi hcompact hcomponent'⟩
    | puncturedProjective =>
      obtain ⟨S⟩ := T.cap₂.nonempty_projective_cover hD
      refine ⟨.realProjectiveThree, ?_⟩
      simpa only [union_comm] using ClosedModels.nonempty_mixed_pair_certificate V W S
        e hes het he hei (union_comm (W : Set M) V ▸ hcompact)
        (union_comm (W : Set M) V ▸ hcomponent')
  | puncturedProjective =>
    obtain ⟨S⟩ := T.cap₁.nonempty_projective_cover hC
    let S' := ClosedModels.projective_cover_of_open_diffeomorph U W E S
    cases hD : T.cap₂.model_kind with
    | euclidean =>
      obtain ⟨e, hes, het, he, hei⟩ := T.cap₂.exists_euclidean_coordinates hD
      exact ⟨.realProjectiveThree, ClosedModels.nonempty_mixed_pair_certificate W V S'
        e hes het he hei hcompact hcomponent'⟩
    | puncturedProjective =>
      obtain ⟨SD⟩ := T.cap₂.nonempty_projective_cover hD
      exact ClosedModels.nonempty_projective_pair_certificate W V S' SD hcompact hcomponent'

end PoincareConjecture.DoubleCappedTubeCertificate
