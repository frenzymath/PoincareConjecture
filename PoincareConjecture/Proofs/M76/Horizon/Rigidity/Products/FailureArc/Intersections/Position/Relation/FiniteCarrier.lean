import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Patches
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteDoubleRelation

set_option autoImplicit false
open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_finite_common_value_complex
    {E F V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f K.space) (hg : PolyhedralPLInCharts e g L.space) :
    ∃ P : SimplicialComplex ℝ (E × F), P.faces.Finite ∧
      P.space = {z | z.1 ∈ K.space ∧ z.2 ∈ L.space ∧ f z.1 = g z.2} := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let : CompactSpace L.space := isCompact_iff_compactSpace.mp (L.isCompact_space_of_finite hL)
  let B : Set (K.space × L.space) := {z | f z.1 = g z.2}
  have hB : IsCompact B := (isClosed_eq
    (hf.continuousOn.domRestrict.comp continuous_fst)
    (hg.continuousOn.domRestrict.comp continuous_snd)).isCompact
  choose P W hP hW hzW hPB hWP using fun z : B =>
    hf.exists_finite_common_value_patch he K L hK hL hg z.val.1 z.val.2 z.property
  obtain ⟨T, hT⟩ := hB.elim_finite_subcover W hW
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩)
  obtain ⟨J, hJ, hJs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion
    (fun z : T => P z) (fun z => hP z)
  refine ⟨J, hJ, hJs.trans ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := mem_iUnion.mp hz
    exact hPB a ha
  · intro hz
    let pair : K.space × L.space := (⟨z.1, hz.1⟩, ⟨z.2, hz.2.1⟩)
    have hpair : pair ∈ B := hz.2.2
    obtain ⟨a, haT, hpa⟩ := mem_iUnion₂.mp (hT hpair)
    exact mem_iUnion.mpr ⟨⟨a, haT⟩, hWP a pair hpa hz.2.2⟩

end Geometry
