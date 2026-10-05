import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleCurve.Mathlib.FiniteDoublePairPatches
import PoincareLib.Topology.Manifold.Smoothing.Dehn.DoubleCurve.Mathlib.CompactDoubleRelation

/-!
# The whole distinct-point relation as an actual finite polyhedron

The diagonal is relatively open in the compact fiber product.
Finitely many actual disjoint source-patch equality loci cover
its compact complement. Their exact finite union is the whole
double relation, including when it is empty. See Dehn032,
section7, and Hudson1969, pp.12--19.
-/

set_option autoImplicit false

open Set

namespace Geometry

/-- The complete distinct-point relation of a locally injective
chartwise PL map from a finite carrier has an exact finite
triangulation in the original source product. Local injectivity
is used only to prove compactness of the actual off-diagonal
relation. No dimension or crossing model is concluded.
See Dehn032, section7. -/
theorem PolyhedralPLInCharts.exists_finite_double_relation_complex
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (hlocal : IsLocallyInjective (fun x : K.space => f x)) :
    ∃ L : SimplicialComplex ℝ (E × E), L.faces.Finite ∧
      L.space = {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
        f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  classical
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let B : Set (K.space × K.space) := {z | f z.1 = f z.2 ∧ z.1 ≠ z.2}
  have hB : IsCompact B := hlocal.isCompact_doubleRelation hf.continuousOn.domRestrict
  choose L W hL hW hzW hLB hWL using fun z : B =>
    hf.exists_finite_double_pair_patch he K hK z.val.1 z.val.2
      z.property.1 z.property.2
  obtain ⟨T, hT⟩ := hB.elim_finite_subcover W hW
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩)
  obtain ⟨J, hJ, hJs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion
    (fun z : T => L z) (fun z => hL z)
  refine ⟨J, hJ, hJs.trans ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := mem_iUnion.mp hz
    exact hLB a ha
  · intro hz
    let pair : K.space × K.space := (⟨z.1, hz.1⟩, ⟨z.2, hz.2.1⟩)
    have hpair : pair ∈ B :=
      ⟨hz.2.2.1, fun h => hz.2.2.2 (congrArg Subtype.val h)⟩
    obtain ⟨a, haT, hpa⟩ := mem_iUnion₂.mp (hT hpair)
    exact mem_iUnion.mpr ⟨⟨a, haT⟩, hWL a pair hpa hz.2.2.1⟩

end Geometry
