import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.State



set_option autoImplicit false
open Set Geometry Metric Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

theorem nonempty_markedEssentialPlanarAnnulus_of_cylinder
    {t : Stage e S f r C} {R : Set M} {F : Bool → Set M}
    (j : (V1 × V2) → t.Carrier) (original : C(source, R))
    (hj : PolyhedralPLInCharts t.charts j source)
    (hemb : IsEmbedding (fun x : source => j x))
    (hvalue : ∀ x : source, (original x : M) = t.projection (j x))
    (hmark : ∀ b (z : sphere (0 : V2) 1), t.projection (j (endpoint b, z)) ∈ F b)
    (hessential : ∀ b, ¬ (sourceAnnulusRim original b).Nullhomotopic)
    (hproper : ∀ x : source, j x ∈ frontier (t.projection ⁻¹' R) ↔
      (x : V1 × V2).1 ∈ sphere (0 : V1) 1) :
    Nonempty (MarkedEssentialPlanarAnnulus t R F) := by
  obtain ⟨K, _, hKs⟩ := exists_source_triangulation
  have hjK : PolyhedralPLInCharts t.charts j K.space := hKs.symm ▸ hj
  have hembK : IsEmbedding (fun x : K.space => j x) :=
    hemb.comp (Homeomorph.setCongr hKs).isEmbedding
  have hregion : MapsTo j K.space (t.projection ⁻¹' R) := by
    intro x hx
    change t.projection (j x) ∈ R
    rw [← hvalue ⟨x, hKs.subset hx⟩]
    exact (original ⟨x, hKs.subset hx⟩).property
  obtain ⟨period, H, g, _, _, hgvalue, hHr, hgPL, hgi, _, hgp, hgm, _⟩ :=
    exists_marked_planar_annulus_reparametrization (F := fun b => t.projection ⁻¹' F b)
      K hKs hjK hembK hregion
      (fun x => hproper ⟨x, hKs.subset x.property⟩) hmark
  let sourceMap : C(Ann, source) :=
    ⟨fun x => (Homeomorph.setCongr hKs) (H x),
      (Homeomorph.setCongr hKs).continuous.comp H.continuous⟩
  let original' := original.comp sourceMap
  refine ⟨{
    map := g
    original := original'
    original_eq := ?_
    piecewiseAffine := hgPL
    embedding := hgi
    proper := hgp
    mark := hgm
    essential := ?_ }⟩
  · intro x
    exact (hvalue (sourceMap x)).trans (congrArg t.projection (hgvalue x).symm)
  · intro b hn
    apply hessential b
    have hcomp : (planarAnnulusRim original' b).comp ⟨period.symm, period.symm.continuous⟩ =
        sourceAnnulusRim original b := by
      apply ContinuousMap.ext
      intro z
      apply congrArg original
      apply Subtype.ext
      change (H (annulusRimPoint b (period.symm z)) : V1 × V2) = _
      rw [hHr, period.apply_symm_apply]
      rfl
    exact hcomp ▸ hn.comp_left ⟨period.symm, period.symm.continuous⟩

end Geometry.OriginalPLTower
