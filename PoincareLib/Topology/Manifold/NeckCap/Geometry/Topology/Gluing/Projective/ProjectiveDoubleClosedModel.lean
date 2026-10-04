import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.ProjectiveDoubleClosedModel.CoverTransport
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.ProjectiveDoubleClosedModel.PositiveAssembly
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.ProjectiveDoubleClosedModel.NegativeClosedModel
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Projective.ProjectiveCompactSide
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Projective.ProjectiveCapCover

/-!
# Closed models of two actual projective caps

The compact-side dichotomy distinguishes a single projective component
from a projective connected sum. The branch producers retain the actual
cover, cut, and collar data of Morgan--Tian A.21, pp. 510-514.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25.Topology3D

/-- The actual compact union of two projective caps has a closed component
model, with its kind selected by the compact-side dichotomy. Both topology
services remain explicit. MT A.21, pp. 510-514; the reviewed existential
assembly derivation dated 2026-09-23. -/
theorem capCertificates_exists_closed_component_of_projective_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (A B : ClosedModelCapData g)
    (hA : A.model_kind = CapModelKind.puncturedProjective)
    (hB : B.model_kind = CapModelKind.puncturedProjective)
    (hcompact : IsCompact (A.carrier ∪ B.carrier)) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (A.carrier ∪ B.carrier)) := by
  obtain ⟨P1⟩ := closedModelCapData_exists_puncturedProjective_cover A hA
  obtain ⟨P2⟩ := closedModelCapData_exists_puncturedProjective_cover B hB
  obtain ⟨v, hv, _haway, hcuts, hh, hleft, hright,
    F, _hFD, hFc, _hFloc, _hFi, _hFdis, _hpreimage,
    hpsi, S, e, hes, _het, _hef, he, hei, hdis, hray, hballs,
    _hretained, hcases⟩ :=
    capCertificates_exists_projective_compact_side_dichotomy hS A B P2 hcompact
  rcases hcases with ⟨hside, hnegative⟩ | ⟨hside, hpositive⟩
  · refine ⟨.realProjectiveThree,
      capCertificates_nonempty_projective_component_of_negative_side
        hS hD A B P1 P2 hcompact ?_⟩
    refine
      { v := v
        v_mem := hv
        cuts := ?_
        F := F
        lift_eq := hFc
        psi := _
        collar := hpsi
        S := S
        side_eq := hside
        e := e
        source_eq := hes
        smooth := he
        inverse_smooth := hei
        disjoint := hdis
        ray := fun q t ht => (hray q t ht).1
        ball_interior := fun t ht => (hballs t ht).2.2.1
        negative := hnegative }
    dsimp only
    intro a b hva hab hbL
    rcases hcuts a b hva hab hbL with
      ⟨_hV, hW, _hclosure, _hinterior, _hc, hsub,
        _hfW, _hfV, hcover, hoverlap, hregion, _hslab⟩
    exact ⟨hW, hsub, hcover, hoverlap, hregion⟩
  · refine ⟨.realProjectiveThreeConnectedSum,
      capCertificates_nonempty_projective_double_of_positive_compact_side
        A B P1 P2 hcompact v ((v + A.epsilon⁻¹) / 2)
        ((A.epsilon⁻¹ - v) / 4) hv hh hleft hright ?_ S e hes he hei hdis ?_⟩
    · intro a b hva hab hbL
      rcases hcuts a b hva hab hbL with
        ⟨_hV, _hW, _hclosure, _hinterior, _hc, hsub,
          _hfW, _hfV, _hcover, _hoverlap, _hregion, hslab⟩
      exact ⟨hsub, hslab⟩
    · have ht : (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) (13 / 16) := by
        constructor <;> norm_num
      simpa only [hside, one_mul, mul_one_div] using (hpositive (1 / 2) ht).2

end PoincareMT.M25.Topology3D
