import PoincareConjecture.Proofs.M25.AppA_21_Local.FiniteCappedChainDiffeomorph
import PoincareConjecture.Proofs.M25.Mathlib.DiffeomorphOnOpens










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem CapCertificate.exists_finite_chain_ambient_chart :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C : CapCertificate g) (D : BalancedNeckChain g C.epsilon) {b : ℤ},
      D.shape = ChainShape.finite 0 b →
      C.epsilon ≤ epsilon0 →
      D.neck 0 = C.end_neck →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      (∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C.carrier) →
      ∃ Phi : OpenPartialHomeomorph M M,
        Phi.source = C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) ∧
        Phi.target = C.carrier ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi
          (C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier)) ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi.symm C.carrier ∧
        EqOn (Phi : M → M) id
          (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) 0) ∧
        EqOn (Phi.symm : M → M) id
          (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) 0) := by
  obtain ⟨epsilon0, hpos, hcap, hFC⟩ :=
    CapCertificate.exists_finite_chain_carrier_diffeomorph.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g C D b hshape hepsilon hstart hsep hout
  let U : TopologicalSpace.Opens M :=
    ⟨C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier),
      C.carrier_open.union
        (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
  let V : TopologicalSpace.Opens M := ⟨C.carrier, C.carrier_open⟩
  obtain ⟨d, hdf, hdi⟩ := hFC C D hshape hepsilon hstart hsep hout
  have hcenter : C.end_neck.center ∈ C.carrier :=
    C.end_neck_subset
      (C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere)
  have hU : Nonempty U := ⟨⟨C.end_neck.center, Or.inl hcenter⟩⟩
  obtain ⟨Phi, hs, ht, hf, hi, hforward, hinverse⟩ :=
    Diffeomorph.exists_openPartialHomeomorph_of_opens (U := U) (V := V) d hU
  change Phi.source = C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier) at hs
  change Phi.target = C.carrier at ht
  have hW : C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) 0 ⊆ C.carrier := by
    rintro x (hx | hx)
    · exact (C.closed_core_eq_complement_end ▸ hx).1
    · exact C.end_neck_subset hx.1
  refine ⟨Phi, hs, ht, ?_, ?_, ?_, ?_⟩
  · exact hs ▸ hf
  · exact ht ▸ hi
  · intro x hx
    exact (hforward x (Or.inl (hW hx))).trans (hdf ⟨x, Or.inl (hW hx)⟩ hx)
  · intro x hx
    exact (hinverse x (hW hx)).trans (hdi ⟨x, hW hx⟩ hx)

end PoincareConjecture
