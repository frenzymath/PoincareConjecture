import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Projective.Decomposition
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Projective.Certificate

/-!
# The projective model of an original mixed two-cap component

A small puncture ball cuts a compact projective piece from the original
projective cap. The actual complementary side lies in the Euclidean cap.
Its ball filling and matching full collar give the global antipodal cover.

Reference: Morgan--Tian, Proposition A.21 and Claims A.23--A.24, pp. 508--514.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

/-- A compact ambient component covered by one projective cap and one
Euclidean cap has its exact smooth projective certificate. -/
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

end PoincareMT.CapCertificate
