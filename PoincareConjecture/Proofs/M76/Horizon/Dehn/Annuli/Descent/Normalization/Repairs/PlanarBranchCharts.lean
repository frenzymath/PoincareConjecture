import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Repairs.BranchCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.ClippedParameters

set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.OriginalRelativeNormalization

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}

theorem exists_annulus_planar_branch_chart
    (D : OriginalRelativeNormalization step K j R Rim)
    (hK : K.faces.Finite) (hKs : K.space = ProtectedAnnulus.source)
    (a b : K.space) (hab : a ≠ b) (hpair : D.projected a = D.projected b)
    {W : Set s.Carrier} (hW : IsOpen W) (haW : D.projected a ∈ W) :
    ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
      (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3),
      D.endpoint a ∈ w.left.source ∧ D.endpoint b ∈ w.right.source ∧
      D.projected a ∈ Q.source ∧ Q (D.projected a) = 0 ∧
      Q.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) ∧
      (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
        (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
      (step.projection ∘ step.inclusion) ⁻¹' Q.source =
        (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∪
          (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' Q.source) ∧
      (∀ y ∈ Q.source, y ∈ (step.projection ∘ step.inclusion) ''
        (D.endpoint '' K.space ∩ w.left.source) ↔ (c (Q y)).2 = 0) ∧
      ∀ J : SimplicialComplex ℝ V3, J.faces.Finite → J.space ⊆ Q.target →
        ∃ (P : SimplicialComplex ℝ V3) (g : V3 → A) (v : V3 → V2),
          P.faces.Finite ∧ P.space = (w.right.trans Q) ''
            (D.endpoint '' K.space ∩ (w.right.trans Q).source) ∩ J.space ∧
          FinitePiecewiseAffineOn g P.space ∧ MapsTo g P.space K.space ∧
          (∀ z ∈ P.space, D.endpoint (g z) ∈ (w.right.trans Q).source ∧
            (w.right.trans Q) (D.endpoint (g z)) = z) ∧
          (∀ z ∈ K.space, D.endpoint z ∈ (w.right.trans Q).source →
            (w.right.trans Q) (D.endpoint z) ∈ J.space →
              g ((w.right.trans Q) (D.endpoint z)) = z) ∧
          FinitePiecewiseAffineOn v P.space ∧ InjOn v P.space ∧
          ∀ z ∈ P.space, z ∈ interior J.space → v z ∈ interior (v '' P.space) := by
  obtain ⟨w, c, Q₀, hal, hbr, haQ₀, hQ₀zero, hQ₀W, hQ₀PL, _, _, hplane, _⟩ :=
    D.exists_annulus_branch_chart hK hKs a b hab hpair hW haW
  have hbint := D.double_point_interior b.property a.property
    (fun h ↦ hab (Subtype.ext h.symm)) hpair.symm
  have hbrim : (b : A).1 ∉ sphere (0 : V1) 1 := by
    intro h
    exact ((D.projected_proper b b.property).mpr ⟨h, (hKs.subset b.property).2⟩).2 hbint
  let eK : K.space ≃ₜ ProtectedAnnulus.source := Homeomorph.setCongr hKs
  obtain ⟨q₀, O, F, hbq₀, hO, hq₀s, _, hq₀val, hF, _⟩ :=
    ProtectedAnnulus.exists_interior_source_parameters (eK b) hbrim
  let q := eK.toOpenPartialHomeomorph.trans q₀
  have hbq : b ∈ q.source := ⟨mem_univ _, hbq₀⟩
  have hqs : q.source = Subtype.val ⁻¹' O := by
    ext x
    change (x ∈ (univ : Set K.space) ∧ eK x ∈ q₀.source) ↔ (x : A) ∈ O
    rw [hq₀s]
    simp only [mem_univ, true_and, mem_preimage]
    rfl
  have hqval (x : K.space) : q x = F x := hq₀val (eK x)
  obtain ⟨V, hV, hqV⟩ := D.endpoint_embedding.isInducing.image_eq_isOpen_inter_range
    q.open_source
  have hbV : D.endpoint b ∈ V := (hqV.subset ⟨b, hbq, rfl⟩).1
  let N := w.right '' (V ∩ w.right.source)
  have hN : IsOpen N := w.right.isOpen_image_of_subset_source
    (hV.inter w.right.open_source) inter_subset_right
  have haN : D.projected a ∈ N := by
    refine ⟨D.endpoint b, ⟨hbV, hbr⟩, ?_⟩
    exact (congrFun w.right_eq _).trans hpair.symm
  let Q := Q₀.restrOpen N hN
  have hQW : Q.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) :=
    fun _ hz ↦ hQ₀W hz.1
  have hQPL (k : s.Index) : (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact (hQ₀PL k).1.mono ((s.charts k).symm.trans Q).open_source
      (fun _ hz ↦ ⟨hz.1, hz.2.1⟩)
  have hbranch (k : t.Index) :
      (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
      (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3 :=
    ⟨step.compatible_branch_chart w.left (fun z _ ↦ congrFun w.left_eq z) Q hQPL k,
      step.compatible_branch_chart w.right (fun z _ ↦ congrFun w.right_eq z) Q hQPL k⟩
  have hfit (x : K.space) (hx : D.endpoint x ∈ (w.right.trans Q).source) :
      x ∈ q.source := by
    obtain ⟨y, ⟨hyV, hyr⟩, hyx⟩ := hx.2.2
    have heq : y = D.endpoint x := w.right.injOn hyr hx.1 hyx
    have hxV : D.endpoint x ∈ V := heq ▸ hyV
    obtain ⟨v, hvq, hvx⟩ := hqV.symm.subset ⟨hxV, ⟨x, rfl⟩⟩
    exact D.endpoint_embedding.injective hvx ▸ hvq
  refine ⟨w, c, Q, hal, hbr, ⟨haQ₀, haN⟩, hQ₀zero, hQW, hQPL, hbranch,
    ?_, fun y hy ↦ hplane y hy.1, ?_⟩
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset (hQW hx).2.2 with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun hx ↦ hx.elim And.right And.right
  · intro J hJ hJQ
    have hJright : J.space ⊆ (w.right.trans Q).target := by
      intro z hz
      refine ⟨hJQ hz, ?_⟩
      change Q.symm z ∈ w.right.target
      rw [w.right_target]
      exact (hQW (Q.map_target (hJQ hz))).2.2
    obtain ⟨P, g, v, hP, hPs, hg, hgK, hright, hleft, hv, hvi, _, hint⟩ :=
      exists_clipped_planar_source_parameter K hK D.endpoint_PL
        (fun x hx y hy hxy ↦ congrArg Subtype.val (D.endpoint_embedding.injective
          (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
        (w.right.trans Q) (fun k ↦ (hbranch k).2) q O F hqs hqval hF hfit J hJ hJright
    exact ⟨P, g, v, hP, hPs, hg, hgK, hright, hleft, hv, hvi, hint⟩

end Geometry.OriginalPLTower.OriginalRelativeNormalization
