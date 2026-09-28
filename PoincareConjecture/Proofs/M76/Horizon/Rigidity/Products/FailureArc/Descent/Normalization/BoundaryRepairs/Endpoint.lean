import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Images
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph



set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}
  {step : Step s t} {j : P2 → t.Carrier} {R Fmark : Set M}
  {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
  (A : PlanarAnnulusBoundaryMotion step j R Fmark a b W ε)


theorem endpoint_properties
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) (hKs : K.space = Ann)
    (hj : PolyhedralPLInCharts t.charts j Ann)
    (hemb : IsEmbedding (fun z : Ann => j z))
    (hDR : MapsTo j Ann (t.projection ⁻¹' R))
    (hproper : ∀ z : Ann, j z ∈ _root_.frontier (t.projection ⁻¹' R) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    (hmark : MapsTo j Rim (t.projection ⁻¹' Fmark)) (u : I) :
    PolyhedralPLInCharts t.charts ((A.ambient u) ∘ j) Ann ∧
      IsEmbedding (fun z : Ann => A.ambient u (j z)) ∧
      MapsTo ((A.ambient u) ∘ j) Ann (t.projection ⁻¹' R) ∧
      (∀ z : Ann, A.ambient u (j z) ∈ _root_.frontier (t.projection ⁻¹' R) ↔
        depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) ∧
      MapsTo ((A.ambient u) ∘ j) Rim (t.projection ⁻¹' Fmark) := by
  have hPL : PolyhedralPLInCharts t.charts ((A.ambient u) ∘ j) Ann := by
    have hjK : PolyhedralPLInCharts t.charts j K.space := hKs.symm ▸ hj
    rw [← hKs]
    exact hjK.comp_chart_homeomorph K hK (A.ambient u) t.cover (A.ambient_PL u)
  refine ⟨hPL, (A.ambient u).isEmbedding.comp hemb, ?_, ?_, ?_⟩
  · intro z hz
    change j z ∈ (A.ambient u) ⁻¹' (t.projection ⁻¹' R)
    rw [A.region]
    exact hDR hz
  · intro z
    exact (Set.ext_iff.mp (A.frontier u) (j z)).trans (hproper z)
  · intro z hz
    change j z ∈ (A.ambient u) ⁻¹' (t.projection ⁻¹' Fmark)
    rw [A.mark]
    exact hmark hz


theorem compact_change_support :
    ∃ D : Set t.Carrier, IsCompact D ∧
      D ⊆ (step.projection ∘ step.inclusion) ⁻¹' W ∧
      ∀ u, EqOn (A.ambient u) id Dᶜ := by
  let T := A.window.right.trans A.chart
  refine ⟨T.symm '' A.support.space, ?_, ?_, A.outside⟩
  · exact (A.support.isCompact_space_of_finite A.support_finite).image_of_continuousOn
      (T.symm.continuousOn.mono A.support_right_target)
  · rintro x ⟨z, hz, rfl⟩
    have hzQ := A.support_target hz
    have hzright : A.chart.symm z ∈ A.window.right.target :=
      A.window.right_target.symm.subset (A.chart_inside (A.chart.map_target hzQ)).2
    have hproj : (step.projection ∘ step.inclusion) (T.symm z) = A.chart.symm z :=
      (congrFun A.window.right_eq _).symm.trans (A.window.right.right_inv hzright)
    change (step.projection ∘ step.inclusion) (T.symm z) ∈ W
    rw [hproj]
    exact (A.chart_inside (A.chart.map_target hzQ)).1



theorem exists_original_rim_homotopy
    (hj : PolyhedralPLInCharts t.charts j Ann)
    (hmark : MapsTo j Rim (t.projection ⁻¹' Fmark)) :
    ∃ (rim₀ rim₁ : C(Rim, Fmark)) (eta : rim₀.Homotopy rim₁),
      (∀ x, (rim₀ x : M) = t.projection (j x)) ∧
      (∀ x, (rim₁ x : M) = t.projection (A.ambient 1 (j x))) ∧
      ∀ u x, (eta (u, x) : M) = t.projection (A.ambient u (j x)) := by
  have hRimAnn : Rim ⊆ Ann := by
    intro z hz
    apply mem_squareAnnulus_iff_depth.mpr
    rcases hz with hz | hz <;> rw [hz] <;> norm_num
  have hjRim : Continuous (fun x : Rim => j x) :=
    (hj.continuousOn.mono hRimAnn).domRestrict
  have hm (u : I) (x : Rim) : t.projection (A.ambient u (j x)) ∈ Fmark := by
    change j x ∈ (A.ambient u) ⁻¹' (t.projection ⁻¹' Fmark)
    rw [A.mark]
    exact hmark x.property
  let rim₀ : C(Rim, Fmark) :=
    ⟨fun x => ⟨t.projection (j x), hmark x.property⟩,
      (t.projection.continuous.comp hjRim).subtype_mk _⟩
  let rim₁ : C(Rim, Fmark) :=
    ⟨fun x => ⟨t.projection (A.ambient 1 (j x)), hm 1 x⟩,
      (t.projection.continuous.comp ((A.ambient 1).continuous.comp hjRim)).subtype_mk _⟩
  let eta : rim₀.Homotopy rim₁ := {
    toFun := fun z => ⟨t.projection (A.ambient z.1 (j z.2)), hm z.1 z.2⟩
    continuous_toFun := (t.projection.continuous.comp
      (A.continuous.comp (continuous_fst.prodMk (hjRim.comp continuous_snd)))).subtype_mk _
    map_zero_left := by intro x; apply Subtype.ext; exact congrArg t.projection (A.zero _)
    map_one_left := fun _ => rfl }
  exact ⟨rim₀, rim₁, eta, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩



theorem exists_original_region_homotopy
    (hj : PolyhedralPLInCharts t.charts j Ann)
    (hDR : MapsTo j Ann (t.projection ⁻¹' R)) :
    ∃ (f₀ f₁ : C(Ann, R)) (H : f₀.Homotopy f₁),
      (∀ x, (f₀ x : M) = t.projection (j x)) ∧
      (∀ x, (f₁ x : M) = t.projection (A.ambient 1 (j x))) ∧
      ∀ u x, (H (u, x) : M) = t.projection (A.ambient u (j x)) := by
  have hm (u : I) (x : Ann) : t.projection (A.ambient u (j x)) ∈ R := by
    change j x ∈ (A.ambient u) ⁻¹' (t.projection ⁻¹' R)
    rw [A.region]
    exact hDR x.property
  let f₀ : C(Ann, R) :=
    ⟨fun x => ⟨t.projection (j x), hDR x.property⟩,
      (t.projection.continuous.comp hj.continuousOn.domRestrict).subtype_mk _⟩
  let f₁ : C(Ann, R) :=
    ⟨fun x => ⟨t.projection (A.ambient 1 (j x)), hm 1 x⟩,
      (t.projection.continuous.comp
        ((A.ambient 1).continuous.comp hj.continuousOn.domRestrict)).subtype_mk _⟩
  let H : f₀.Homotopy f₁ := {
    toFun := fun z => ⟨t.projection (A.ambient z.1 (j z.2)), hm z.1 z.2⟩
    continuous_toFun := (t.projection.continuous.comp
      (A.continuous.comp (continuous_fst.prodMk
        (hj.continuousOn.domRestrict.comp continuous_snd)))).subtype_mk _
    map_zero_left := by intro x; apply Subtype.ext; exact congrArg t.projection (A.zero _)
    map_one_left := fun _ => rfl }
  exact ⟨f₀, f₁, H, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
