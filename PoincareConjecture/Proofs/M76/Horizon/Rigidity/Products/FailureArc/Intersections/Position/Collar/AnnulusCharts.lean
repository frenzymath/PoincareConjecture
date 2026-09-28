import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.AnnulusCarrier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.ChartStars



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem exists_regular_planar_annulus_collar_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Source K : SimplicialComplex ℝ V2) (hSource : Source.faces.Finite) (hK : K.faces.Finite)
    (hKs : K.space = squareAnnulus 8 1)
    {f g : V2 → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hg : PolyhedralPLInCharts e g K.space) (hfi : InjOn f Source.space) (hgi : InjOn g K.space)
    (mark : Set X) (hmark : IsClosed mark)
    (hproper : ∀ x ∈ K.space, g x ∈ mark → x ∈ frontier (squareAnnulus 8 1))
    (hboundary : ∀ x ∈ frontier (squareAnnulus 8 1), g x ∈ f '' Source.space →
      Nonempty (OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) true))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : ℝ) (R L : SimplicialComplex ℝ V2),
      0 < c ∧ c < δ ∧ R.faces.Finite ∧ R.IsSubdivision K ∧
      R.space = squareAnnulus 8 1 ∧ L ≤ R ∧ L.faces.Finite ∧
      L.space = squareAnnulus 8 1 ∩ {x | planarAnnulusRimHeight x ≤ c} ∧
      frontier (squareAnnulus 8 1) ⊆ L.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) ∧
      {x | x ∈ squareAnnulus 8 1 ∧ g x ∈ f '' Source.space ∧ planarAnnulusRimHeight x = c}.Finite ∧
      (∀ p ∈ R.vertices, ∃ B : OpenPartialHomeomorph X V3,
        MapsTo g (R.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (R.closedStar p).AffineOnFaces (B ∘ g)) ∧
      ∀ s ∈ R.faces, s ∉ L.faces →
        ∃ (B : OpenPartialHomeomorph X V3) (A : V2 →ᴬ[ℝ] V3),
          (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
          Disjoint B.source mark ∧ MapsTo g (convexHull ℝ (s : Set V2)) B.source ∧
          EqOn (B ∘ g) A (convexHull ℝ (s : Set V2)) := by
  obtain ⟨c, R₀, M, _, hc, hcδ, hR₀, hR₀K, hR₀s, _, hM, hMs, hrimM,
      _, _, _, _, _, hfinite, _⟩ :=
    exists_regular_planar_annulus_intersection_collar he Source K hSource hK hKs
      hf hg hfi hgi hboundary hδ
  have hgR : PolyhedralPLInCharts e g R₀.space := hR₀K.space_eq.symm ▸ hg
  have hgiR : InjOn g R₀.space := hR₀K.space_eq.symm ▸ hgi
  have hMlevel : M.space = R₀.space ∩ {x | planarAnnulusRimHeight x ≤ c} := by
    rw [hR₀s]
    exact hMs
  obtain ⟨R, L, hR, hRR₀, hLR, hLs, hfull, hstars, hfaces⟩ :=
    exists_collar_adapted_original_chart_stars he R₀ M hR₀ hM hgR hgiR mark hmark
      continuous_planarAnnulusRimHeight hc hMlevel (by
        intro x hx hxmark
        apply (planarAnnulusRimHeight_eq_zero_iff (hR₀s.subset hx)).mpr
        exact hproper x (hR₀K.space_eq.subset hx) hxmark)
  refine ⟨c, R, L, hc, hcδ, hR, hRR₀.trans hR₀K, hRR₀.space_eq.trans hR₀s,
    hLR, hR.subset hLR, hLs.trans hMs, hrimM.trans hLs.symm.subset,
    hfull, hfinite, ?_, hfaces⟩
  exact hstars

end PoincareConjecture.M76
