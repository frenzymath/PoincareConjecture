import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Tube.Absorption
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Tube.Straightening










noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapTubeAttachment



theorem exists_absorption_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {X : Set M},
        ∀ {C : CapCertificate g} {T : EpsilonTubeCertificate g X} {side : Bool},
          CapTubeAttachment C T side → C.epsilon ≤ ε₀ →
          let U : Opens M := ⟨C.carrier, C.carrier_open⟩
          let V : Opens M := ⟨T.carrier, T.carrier_open⟩
          ∃ s ∈ Ioo 0 C.epsilon⁻¹,
            ∃ D : Diffeomorph (𝓡 3) (𝓡 3) U (↥(U ⊔ V)) ∞,
              (∀ x : U,
                (x : M) ∈ C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s) →
                  (D x : M) = x) ∧
              ∀ x : U, (x : M) ∈ C.closed_core → (D x : M) = x := by
  obtain ⟨ε₀, hε₀, hsmall, hstraight⟩ := exists_tube_collar_straightening_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g X C T side A hC
  let U : Opens M := ⟨C.carrier, C.carrier_open⟩
  let V : Opens M := ⟨T.carrier, T.carrier_open⟩
  let W := U ⊓ V
  obtain ⟨s, hs, δ, hδ, hlo, hhi, htail, r, hr, hrδ, F, G, hFval, hGval,
      hK, hKC, hcore, hfront, houtside, hUdiff, hFnegative, hFclosed,
      hGnegative, hGclosed⟩ := hstraight A hC
  let K := C.closed_core ∪ closure (C.end_neck.region (-C.epsilon⁻¹) s)
  have hfrontF : frontier K = range (fun q : UnitTwoSphere => (F (q, 0) : M)) := by
    rw [hfront]
    congr 1
    funext q
    simpa only [add_zero] using (hFval (q, 0) (by simpa using hr)).symm
  obtain ⟨D, hDK, _⟩ := Poincare.exists_absorption_of_matching_cylinders
    U W V hK.isClosed hKC inter_subset_left inter_subset_right houtside
    F G hFclosed hGclosed hfrontF hr
    (fun p hp => (hFval p hp).trans (hGval p hp).symm)
  exact ⟨s, hs, D, hDK, fun x hx => hDK x (Or.inl hx)⟩

end PoincareConjecture.CapTubeAttachment
