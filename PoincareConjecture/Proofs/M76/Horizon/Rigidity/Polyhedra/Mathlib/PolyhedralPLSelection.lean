import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Affine.Mathlib.ContinuousAffineSelection
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart










set_option autoImplicit false

open Set

namespace Geometry

variable {E X ι ν : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X] [Fintype ν]
  {e : ι → OpenPartialHomeomorph X (ν → ℝ)}

private theorem selection_coordinates
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (ν → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f₀ f₁ g : E → X} (h₀ : PolyhedralPLInCharts e f₀ K.space)
    (h₁ : PolyhedralPLInCharts e f₁ K.space) (hg : ContinuousOn g K.space)
    (hselect : ∀ y ∈ K.space, g y = f₀ y ∨ g y = f₁ y)
    (x : K.space) (hx : g x = f₀ x) :
    ∃ (i : ι) (N : SimplicialComplex ℝ E) (V : Set K.space),
      N.faces.Finite ∧ N.space ⊆ K.space ∧ IsOpen V ∧ x ∈ V ∧
      (Subtype.val : K.space → E) '' V ⊆ N.space ∧
      MapsTo g N.space (e i).source ∧ FinitePiecewiseAffineOn ((e i) ∘ g) N.space := by
  classical
  obtain ⟨i, hxi⟩ := hcover (f₀ x)
  by_cases heq : f₀ x = f₁ x
  · let U : Set K.space := {y | f₀ y ∈ (e i).source ∧ f₁ y ∈ (e i).source}
    have hU : IsOpen U :=
      ((e i).open_source.preimage h₀.continuousOn.domRestrict).inter
        ((e i).open_source.preimage h₁.continuousOn.domRestrict)
    obtain ⟨N, V, hN, hNK, hV, hxV, hVN, hNU⟩ :=
      K.exists_relative_polyhedral_neighborhood hK x hU ⟨hxi, heq ▸ hxi⟩
    have h₀i (y : E) (hy : y ∈ N.space) : f₀ y ∈ (e i).source :=
      (hNU (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).1
    have h₁i (y : E) (hy : y ∈ N.space) : f₁ y ∈ (e i).source :=
      (hNU (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).2
    have hgi : MapsTo g N.space (e i).source := by
      intro y hy
      exact (hselect y (hNK hy)).elim (fun h => h ▸ h₀i y hy) (fun h => h ▸ h₁i y hy)
    have h₀PL := (h₀.restrict_finite N hN hNK).finitePiecewiseAffineOn_fixed_chart
      hcompat N hN i h₀i
    have h₁PL := (h₁.restrict_finite N hN hNK).finitePiecewiseAffineOn_fixed_chart
      hcompat N hN i h₁i
    refine ⟨i, N, V, hN, hNK, hV, hxV, hVN, hgi, ?_⟩
    exact h₀PL.continuous_selection_pi h₁PL
      ((e i).continuousOn.comp (hg.mono hNK) hgi) (fun y hy =>
        (hselect y (hNK hy)).imp (congrArg (e i)) (congrArg (e i)))
  · let U : Set K.space := {y | f₀ y ∈ (e i).source ∧ g y ≠ f₁ y}
    have hU : IsOpen U := ((e i).open_source.preimage h₀.continuousOn.domRestrict).inter
      (isClosed_eq hg.domRestrict h₁.continuousOn.domRestrict).isOpen_compl
    obtain ⟨N, V, hN, hNK, hV, hxV, hVN, hNU⟩ :=
      K.exists_relative_polyhedral_neighborhood hK x hU ⟨hxi, by simpa only [hx] using heq⟩
    have h₀i (y : E) (hy : y ∈ N.space) : f₀ y ∈ (e i).source :=
      (hNU (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).1
    have hagree : EqOn g f₀ N.space := by
      intro y hy
      exact (hselect y (hNK hy)).resolve_right
        (hNU (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)).2
    refine ⟨i, N, V, hN, hNK, hV, hxV, hVN,
      fun y hy => hagree hy ▸ h₀i y hy, ?_⟩
    exact ((h₀.restrict_finite N hN hNK).finitePiecewiseAffineOn_fixed_chart
      hcompat N hN i h₀i).congr (fun y hy => congrArg (e i) (hagree hy).symm)



theorem PolyhedralPLInCharts.continuous_selection
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (ν → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f₀ f₁ g : E → X} (h₀ : PolyhedralPLInCharts e f₀ K.space)
    (h₁ : PolyhedralPLInCharts e f₁ K.space) (hg : ContinuousOn g K.space)
    (hselect : ∀ y ∈ K.space, g y = f₀ y ∨ g y = f₁ y) :
    PolyhedralPLInCharts e g K.space := by
  refine ⟨hg, ?_⟩
  intro x
  rcases hselect x x.property with hx | hx
  · exact selection_coordinates hcover hcompat K hK h₀ h₁ hg hselect x hx
  · exact selection_coordinates hcover hcompat K hK h₁ h₀ hg
      (fun y hy => (hselect y hy).symm) x hx

end Geometry
