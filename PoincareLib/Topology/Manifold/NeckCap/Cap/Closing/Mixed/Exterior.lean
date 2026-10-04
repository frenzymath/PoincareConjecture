import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Exterior.Matching
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Projective.Gluing
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Projective.Certificate

/-!
# Projective closing when the original exterior lies in a Euclidean cap

The actual complementary side is filled in the Euclidean cap, matched to
the original projective neck, and glued to the retained antipodal cover.
The resulting certificate describes the original ambient component.

Reference: Morgan--Tian, Proposition A.21 and Claims A.23--A.24, pp. 508--514.
-/

noncomputable section
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

/-- The original projective core with compact exterior in a Euclidean cap
has an exact projective certificate on its entire ambient component. -/
theorem nonempty_projective_certificate_of_exterior_in_euclidean_cap
    (C D : CapCertificate g) (hC : C.model_kind = .puncturedProjective)
    (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact
      (closure (connectedComponent C.boundary_neck.center \ C.closed_core)))
    (hsub : closure (connectedComponent C.boundary_neck.center \ C.closed_core) ⊆
      D.carrier) :
    Nonempty (ClosedComponentCertificate .realProjectiveThree
      (connectedComponent C.boundary_neck.center)) := by
  obtain ⟨S⟩ := C.nonempty_projective_cover hC
  obtain ⟨a, ha⟩ := Quotient.mk'_surjective C.puncture
  obtain ⟨r, b, v, hr, hbs, hvs, _, hb, hbi, hv, hvi, _, hbclosed, hbopen,
    hvclosed, _, _, hdisjoint, hmatch⟩ :=
    C.exists_matching_exterior_ball_in_euclidean_cap S a ha D hD hcompact hsub
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E3 M
  let Y : Opens M := ⟨connectedComponent C.boundary_neck.center, isOpen_connectedComponent⟩
  have hY : (Y : Set M) = C.closed_core ∪ v '' Metric.closedBall 0 1 := by
    rw [hvclosed, C.closed_core_union_closure_exterior]
    rfl
  obtain ⟨P, _, _⟩ := C.exists_projective_cover_of_matching_exterior_ball S a ha b
    hbs hb hbi hbclosed hbopen v hvs hv hvi hr hmatch hdisjoint Y hY
  apply P.nonempty_closedComponentCertificate Y
  · change IsCompact (connectedComponent C.boundary_neck.center)
    rw [← C.closed_core_union_closure_exterior]
    exact C.closed_core_compact.union hcompact
  · exact ⟨C.boundary_neck.center, rfl⟩

end PoincareMT.CapCertificate
