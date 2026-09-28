import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.OriginalTube

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem nonempty_originalIntervalTube
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    (he : PLDomain e R)
    (K₀ K₁ : SimplicialComplex ℝ P2) (hK₀ : K₀.faces.Finite) (hK₁ : K₁.faces.Finite)
    (f₀ f₁ : P2 → X) (hf₀ : PolyhedralPLInCharts e f₀ K₀.space)
    (hf₁ : PolyhedralPLInCharts e f₁ K₁.space)
    (hf₀i : InjOn f₀ K₀.space) (hf₁i : InjOn f₁ K₁.space)
    (hR₀ : MapsTo f₀ K₀.space R) (hR₁ : MapsTo f₁ K₁.space R)
    (Q₀ Q₁ : Set P2) (hQ₀ : Q₀ ⊆ K₀.space) (hQ₁ : Q₁ ⊆ K₁.space)
    (hproper₀ : ∀ x ∈ K₀.space, f₀ x ∈ frontier R ↔ x ∈ Q₀)
    (hproper₁ : ∀ x ∈ K₁.space, f₁ x ∈ frontier R ↔ x ∈ Q₁)
    (hboundary : ∀ x ∈ K₀.space, f₀ x ∈ f₁ '' K₁.space → f₀ x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f₀ '' K₀.space) (f₁ '' K₁.space) (f₀ x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔
          0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔
          (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ K₀.space, f₀ x ∈ f₁ '' K₁.space → f₀ x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f₀ '' K₀.space) (f₁ '' K₁.space) (f₀ x) false))
    (C D : Set P2) (hC : C ⊆ K₀.space) (hD : D ⊆ K₁.space)
    (hball : IsFinitePLBallPair ℝ C (C ∩ Q₀)) (himage : f₀ '' C = f₁ '' D)
    (hrest : IsClosed ((K₀.space ∩ f₀ ⁻¹' (f₁ '' K₁.space)) \ C))
    (hW : IsOpen W) (hCW : f₀ '' C ⊆ W) :
    Nonempty (OriginalIntervalTube e R W K₀.space K₁.space C D f₀ f₁) := by
  obtain ⟨a,L,f,hdis,hL,hLs,hf,hkeep₀,hkeep₁,hin,hfront,hdouble,⟨old⟩⟩ :=
    exists_copied_proper_source_model he.compatible K₀ K₁ hK₀ hK₁ f₀ f₁ hf₀ hf₁
      hf₀i hf₁i hR₀ hR₁ Q₀ Q₁ hQ₀ hQ₁ hproper₀ hproper₁ hboundary hinterior
  obtain ⟨c,τ,hc,hc₀,hc₁,hτ,hτi,hτR,hτW,hval,hpre,hcenter₀,hcenter₁,hτfront⟩ :=
    exists_copied_selected_interval_tube he a
      (K₀.isCompact_space_of_finite hK₀) (K₁.isCompact_space_of_finite hK₁) hdis
      hf₀.continuousOn hf₁.continuousOn hf₀i hf₁i (hLs ▸ hf) hkeep₀ hkeep₁
      hQ₁ hC hD hball himage hrest (hLs ▸ hdouble) (hLs ▸ old)
      (hLs ▸ hin) (hLs ▸ hfront) hW hCW
  exact nonempty_originalIntervalTube_of_copied a hdis hkeep₀ hkeep₁ c τ hc hc₀ hc₁
    hτ hτi hτR hτW hval hpre hcenter₀ hcenter₁ hτfront

end PoincareConjecture.M76.Dehn.Annuli
