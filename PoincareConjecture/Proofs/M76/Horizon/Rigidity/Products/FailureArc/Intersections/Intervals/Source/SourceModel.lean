import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Charts.CopiedCrossings
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SourceCopies
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.CopiedFibers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.Decomposition



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_copied_proper_source_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K₀ K₁ : SimplicialComplex ℝ P2) (hK₀ : K₀.faces.Finite) (hK₁ : K₁.faces.Finite)
    (f₀ f₁ : P2 → X) (hf₀ : PolyhedralPLInCharts e f₀ K₀.space)
    (hf₁ : PolyhedralPLInCharts e f₁ K₁.space)
    (hf₀i : InjOn f₀ K₀.space) (hf₁i : InjOn f₁ K₁.space)
    (hR₀ : MapsTo f₀ K₀.space R) (hR₁ : MapsTo f₁ K₁.space R)
    (Q₀ Q₁ : Set P2) (hQ₀ : Q₀ ⊆ K₀.space) (hQ₁ : Q₁ ⊆ K₁.space)
    (hproper₀ : ∀ x ∈ K₀.space, f₀ x ∈ frontier R ↔ x ∈ Q₀)
    (hproper₁ : ∀ x ∈ K₁.space, f₁ x ∈ frontier R ↔ x ∈ Q₁)
    (hboundary : ∀ x ∈ K₀.space, f₀ x ∈ f₁ '' K₁.space → f₀ x ∈ frontier R →
      ∃ C : OriginalSurfacePairChart e (f₀ '' K₀.space) (f₁ '' K₁.space) (f₀ x) true,
        (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔
          0 ≤ (C.coordinates z).1.2) ∧
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔
          (C.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ K₀.space, f₀ x ∈ f₁ '' K₁.space → f₀ x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f₀ '' K₀.space) (f₁ '' K₁.space) (f₀ x) false)) :
    ∃ (a : P2 ≃ᴬ[ℝ] P2) (L : SimplicialComplex ℝ P2) (f : P2 → X),
      Disjoint K₀.space (a '' K₁.space) ∧ L.faces.Finite ∧
      L.space = K₀.space ∪ a '' K₁.space ∧ PolyhedralPLInCharts e f L.space ∧
      EqOn f f₀ K₀.space ∧ (∀ x ∈ K₁.space, f (a x) = f₁ x) ∧
      MapsTo f L.space R ∧
      (∀ x ∈ L.space, f x ∈ frontier R ↔ x ∈ Q₀ ∪ a '' Q₁) ∧
      doubleLocusOn f L.space = (K₀.space ∩ f₀ ⁻¹' (f₁ '' K₁.space)) ∪
        a '' (K₁.space ∩ f₁ ⁻¹' (f₀ '' K₀.space)) ∧
      Nonempty (SourceDoubleComponents e f L.space (Q₀ ∪ a '' Q₁) R) := by
  classical
  have hS₀ := K₀.isCompact_space_of_finite hK₀
  have hS₁ := K₁.isCompact_space_of_finite hK₁
  obtain ⟨a,L,f,hdis,hL,hLs,hf,hkeep₀,hkeep₁⟩ :=
    exists_disjoint_planar_source_map he K₀ K₁ hK₀ hK₁ f₀ f₁ hf₀ hf₁
  obtain ⟨hi₀,hi₁,hdouble⟩ := copied_pair_double_locus a hdis hf₀i hf₁i hkeep₀ hkeep₁ rfl rfl
  have hin : MapsTo f L.space R := by
    intro x hx
    rcases hLs.subset hx with hx | ⟨y,hy,rfl⟩
    · rw [hkeep₀ hx]
      exact hR₀ hx
    · rw [hkeep₁ y hy]
      exact hR₁ hy
  have hproper : ∀ x ∈ L.space, f x ∈ frontier R ↔ x ∈ Q₀ ∪ a '' Q₁ := by
    intro x hx
    rcases hLs.subset hx with hx | ⟨y,hy,rfl⟩
    · rw [hkeep₀ hx,hproper₀ x hx]
      constructor
      · exact Or.inl
      · rintro (h | ⟨z,hz,hzx⟩)
        · exact h
        · exact (disjoint_left.mp hdis hx ⟨z,hQ₁ hz,hzx⟩).elim
    · rw [hkeep₁ y hy,hproper₁ y hy]
      constructor
      · exact fun h => Or.inr ⟨y,h,rfl⟩
      · rintro (h | ⟨z,hz,hzy⟩)
        · exact (disjoint_left.mp hdis (hQ₀ h) ⟨y,hy,rfl⟩).elim
        · exact a.injective hzy ▸ hz
  have hdoubleL : doubleLocusOn f L.space =
      (K₀.space ∩ f₀ ⁻¹' (f₁ '' K₁.space)) ∪
        a '' (K₁.space ∩ f₁ ⁻¹' (f₀ '' K₀.space)) := by
    rw [hLs]
    exact hdouble
  have hclosed : IsClosed (doubleLocusOn f L.space) := by
    rw [hdoubleL]
    have hC := hf₀.continuousOn.preimage_isClosed_of_isClosed hS₀.isClosed
      (hS₁.image_of_continuousOn hf₁.continuousOn).isClosed
    have hD := hf₁.continuousOn.preimage_isClosed_of_isClosed hS₁.isClosed
      (hS₀.image_of_continuousOn hf₀.continuousOn).isClosed
    exact hC.union (a.toHomeomorph.isClosedMap _ hD)
  have hcross := copied_proper_pair_raw_crossings a hS₀ hS₁ hf₀i hf₁i hdis
    (hLs ▸ hf.continuousOn) hkeep₀ hkeep₁ hR₀ hboundary hinterior
  refine ⟨a,L,f,hdis,hL,hLs,hf,hkeep₀,hkeep₁,hin,hproper,hdoubleL,?_⟩
  apply nonempty_sourceDoubleComponents he L hL (Q₀ ∪ a '' Q₁) hf hin hclosed hproper
  · exact hLs.symm ▸ hcross
  · intro x hx y hy z hz hxy hxz hfxy hfxz
    exact disjoint_source_pair_unique hdis hi₀ hi₁ (hLs.subset hx) (hLs.subset hy)
      (hLs.subset hz) hxy hxz hfxy hfxz

end PoincareConjecture.M76.Dehn.Annuli
