import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Assembly.ExceptionRepair



set_option autoImplicit false
open Set Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => PLAnnularStrip.squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => PLAnnularStrip.depth 8 z = -1 ∨
  PLAnnularStrip.depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ P2} {j : P2 → t.Carrier} {R Fmark : Set M}

theorem MarkedSurfacePositionData.exists_annulus_boundary_exception_repair
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hAnn : D.K.space = Ann) (hRim : A₀.space = Rim)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (a b : Ann) (hab : a ≠ b) (haRim : (a : P2) ∈ Rim)
    (hpair : D.projected a = D.projected b)
    {W : Set s.Carrier} (hWopen : IsOpen W) (haW : D.projected a ∈ W)
    (hW : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
      (Small : Set t.Carrier),
      IsCompact Small ∧ IsCompact (Small ∪ N.ambient 1 '' Small) ∧
      Small ∪ N.ambient 1 '' Small ⊆ (step.projection ∘ step.inclusion) ⁻¹' W ∧
      D.projected a ∈ (step.projection ∘ step.inclusion) '' Small ∧
      (∀ u, EqOn (N.ambient u) id (D.endpoint '' D.K.space \ Small)) ∧
      ∀ x y : D.K.space, x ≠ y →
        (step.projection ∘ step.inclusion) (N.ambient 1 (D.endpoint x)) =
          (step.projection ∘ step.inclusion) (N.ambient 1 (D.endpoint y)) →
        (step.projection ∘ step.inclusion) (N.ambient 1 (D.endpoint x)) ∈
          (step.projection ∘ step.inclusion) '' (Small ∪ N.ambient 1 '' Small) →
        ∃ B : ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
          (N.ambient 1 ∘ D.endpoint) D.K.space (s.projection ⁻¹' R) x y,
          B.chart.source ⊆ W := by
  have hj : PolyhedralPLInCharts t.charts D.endpoint Ann :=
    hAnn ▸ (D.states D.length).original_PL
  have hemb : IsEmbedding (fun x : Ann => D.endpoint x) :=
    (D.states D.length).embedding.comp (Homeomorph.setCongr hAnn.symm).isEmbedding
  have hregion : MapsTo D.endpoint Ann (t.projection ⁻¹' R) := by
    rw [← hAnn]
    exact (D.states D.length).region
  have hproper (x : Ann) : D.endpoint x ∈ frontier (t.projection ⁻¹' R) ↔
      PLAnnularStrip.depth 8 (x : P2) = -1 ∨ PLAnnularStrip.depth 8 (x : P2) = 1 := by
    have h := (D.states D.length).proper x (hAnn.symm.subset x.property)
    change D.endpoint x ∈ frontier (t.projection ⁻¹' R) ↔ (x : P2) ∈ A₀.space at h
    rw [hRim] at h
    exact h
  have hmark : MapsTo D.endpoint Rim (t.projection ⁻¹' Fmark) := by
    rw [← hRim]
    exact (D.states D.length).mark
  obtain ⟨N⟩ := step.nonempty_planar_annulus_boundary_motion he hF hopen
    D.K D.source_finite hAnn hj hemb hregion hproper hmark a b hab haRim
    hpair hWopen haW ε hε
  obtain ⟨Small, hSmall, hEnd, hSmallW, hcenter, hfix, hcross⟩ :=
    N.exists_crossed_change_support hAnn hRim hWopen hW
  exact ⟨N, Small, hSmall, hEnd, hSmallW, hcenter, hfix, hcross⟩

end Geometry.OriginalPLTower
