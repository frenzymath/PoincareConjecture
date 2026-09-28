import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension
import Mathlib.Topology.LocallyFinite








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CyclicPanels

theorem exists_original_panel_pasting
    {E V X ι σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [Finite σ]
    {e : ι → OpenPartialHomeomorph X V}
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : σ → SimplicialComplex ℝ E) (hK : ∀ i, (K i).faces.Finite)
    (f : σ → E → X) (base : X)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) (K i).space)
    (hagree : ∀ i j x, x ∈ (K i).space → x ∈ (K j).space → f i x = f j x) :
    ∃ g : E → X,
      PolyhedralPLInCharts e g (⋃ i, (K i).space) ∧
      (∀ i, EqOn g (f i) (K i).space) ∧
      g '' (⋃ i, (K i).space) = ⋃ i, f i '' (K i).space ∧
      ∀ W : Set X, (⋃ i, (K i).space) ∩ g ⁻¹' W =
        ⋃ i, (K i).space ∩ (f i) ⁻¹' W := by
  classical
  let g : E → X := fun x ↦ if hx : x ∈ ⋃ i, (K i).space then
    f (mem_iUnion.mp hx).choose x else base
  have hvalue (i : σ) : EqOn g (f i) (K i).space := by
    intro x hx
    have hxU : x ∈ ⋃ i, (K i).space := mem_iUnion.mpr ⟨i, hx⟩
    dsimp only [g]
    rw [dif_pos hxU]
    exact hagree _ i x (mem_iUnion.mp hxU).choose_spec hx
  have hpiece (i : σ) : PolyhedralPLInCharts e g (K i).space :=
    (hf i).congr (fun x hx ↦ (hvalue i hx).symm)
  obtain ⟨J, hJ, hJs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion K hK
  have hgc : ContinuousOn g (⋃ i, (K i).space) :=
    (locallyFinite_of_finite _).continuousOn_iUnion
      (fun i ↦ (K i).isCompact_space_of_finite (hK i) |>.isClosed)
      (fun i ↦ (hpiece i).continuousOn)
  have hg := polyhedralPLInCharts_of_finite_cover hcover hcompat J hJ K hK
    (hJs.symm ▸ hgc) hpiece hJs.subset
  refine ⟨g, hJs ▸ hg, hvalue, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, x, hi, (hvalue i hi).symm⟩
    · intro hy
      obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hy
      exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩, hvalue i hx⟩
  · intro W
    ext x
    constructor
    · rintro ⟨hx, hW⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, hi, by simpa only [mem_preimage, hvalue i hi] using hW⟩
    · intro hx
      obtain ⟨i, hi, hW⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨i, hi⟩, by simpa only [mem_preimage, hvalue i hi] using hW⟩

end PoincareConjecture.M76.Dehn.Annuli.CyclicPanels
