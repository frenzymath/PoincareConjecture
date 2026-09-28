import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorRepairs.ExceptionRepair









set_option autoImplicit false
open Set Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ A} {j : A → t.Carrier} {R Fmark : Set M}

theorem MarkedSurfacePositionData.exists_interior_exception_repair
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hboundary : A₀.space = frontier K₀.space)
    (a b : D.K.space) (hab : a ≠ b) (hpair : D.projected a = D.projected b)
    (haint : D.projected a ∈ interior (s.projection ⁻¹' R))
    {W : Set s.Carrier} (hWopen : IsOpen W) (haW : D.projected a ∈ W)
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : PlanarSurfaceBranchMotion step D.K D.endpoint R a b W ε) (Small : Set t.Carrier),
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
  have hproper : ∀ x ∈ D.K.space,
      D.endpoint x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ frontier D.K.space := by
    intro x hx
    rw [D.source_space, ← hboundary]
    exact (D.states D.length).proper x hx
  obtain ⟨N⟩ := step.nonempty_planar_surface_branch_motion D.source_finite
    (D.states D.length).original_PL (D.states D.length).embedding hproper
    a b hab hpair haint hWopen haW ε hε
  obtain ⟨Small, hSmall, hEnd, hSmallW, hcenter, hfix, hcross⟩ :=
    N.exists_crossed_change_support hWopen hW
  exact ⟨N, Small, hSmall, hEnd, hSmallW, hcenter, hfix, hcross⟩

end Geometry.OriginalPLTower
