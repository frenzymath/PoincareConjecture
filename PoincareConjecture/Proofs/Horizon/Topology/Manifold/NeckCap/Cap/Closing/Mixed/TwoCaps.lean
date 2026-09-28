import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Projective.Decomposition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Projective.Certificate











set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem nonempty_mixed_cap_closedComponentCertificate (C D : CapCertificate g)
    (hC : C.model_kind = .puncturedProjective) (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact (C.carrier ∪ D.carrier))
    (hcomponent : ∃ x : M, C.carrier ∪ D.carrier = connectedComponent x) :
    Nonempty (ClosedComponentCertificate .realProjectiveThree (C.carrier ∪ D.carrier)) := by
  obtain ⟨S⟩ := C.nonempty_projective_cover hC
  obtain ⟨a, ha⟩ := Quotient.mk'_surjective C.puncture
  obtain ⟨r, b, v, hr, hbs, hvs, hb0, hb, hbi, hv, hvi, hBB, hdisjoint, hcover, hmatch⟩ :=
    C.exists_two_cap_projective_matching_ball D S a ha hD hcompact
  let Y : Opens M := ⟨C.carrier ∪ D.carrier, C.carrier_open.union D.carrier_open⟩
  obtain ⟨P, _, _⟩ := ProjectiveGluing.exists_smooth_cover_of_matching_ball S a ha b hbs hb hbi
    hb0 hBB v hvs hv hvi hr hmatch hdisjoint Y hcover
  exact P.nonempty_closedComponentCertificate Y hcompact hcomponent

end PoincareConjecture.CapCertificate
