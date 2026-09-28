import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MixedCompatibleChartPatch
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.CollarMesh

theorem exists_mixed_chart_extension_with_ambient_window
    {D E V X ι : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V}
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {g : D → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : OpenPartialHomeomorph X E)
    (hQ : ∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans Q) ((e i).symm.trans Q).source)
    (x : K.space) (hxQ : g x ∈ Q.source)
    {U : Set X} (hU : IsOpen U) (hxU : g x ∈ U) :
    ∃ (f : D → E) (O : Set X),
      FinitePiecewiseAffineOn f K.space ∧ IsOpen O ∧ g x ∈ O ∧
      O ⊆ U ∩ Q.source ∧ ∀ z ∈ K.space, g z ∈ O → f z = Q (g z) := by
  classical
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, _, hcoords⟩ :=
    hg.exists_finite_mixed_chart_patch K hK Q hQ x hxQ
  obtain ⟨f, hf, hfQ, _, _⟩ := hcoords.exists_supported_extension K hK hNK
    isOpen_univ (subset_univ _)
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp
    (K.isCompact_space_of_finite hK)
  let bad := (fun z : K.space => g z) '' Wᶜ
  have hbad : IsCompact bad := hW.isClosed_compl.isCompact.image hg.continuousOn.domRestrict
  let O := (U ∩ Q.source) ∩ badᶜ
  have hxgood : g x ∉ bad := by
    rintro ⟨z, hz, heq⟩
    have hzx : z = x := Subtype.ext (hgi z.property x.property heq)
    exact hz (hzx.symm ▸ hxW)
  refine ⟨f, O, hf, (hU.inter Q.open_source).inter hbad.isClosed.isOpen_compl,
    ⟨⟨hxU, hxQ⟩, hxgood⟩, inter_subset_left, ?_⟩
  intro z hz hzO
  have hzW : (⟨z, hz⟩ : K.space) ∈ W := by
    by_contra hn
    exact hzO.2 ⟨⟨z, hz⟩, hn, rfl⟩
  exact hfQ (hWN ⟨⟨z, hz⟩, hzW, rfl⟩)

end PoincareConjecture.M76.CollarMesh
