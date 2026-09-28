import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierComponentLabels
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover












set_option autoImplicit false

open Set Geometry Topology

namespace Geometry

theorem compatiblePLCharts_trans
    {X E ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (e : ι → OpenPartialHomeomorph X E)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (H J : OpenPartialHomeomorph X E)
    (hH : ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E)
    (hJ : ∀ i, (e i).symm.trans J ∈ piecewiseAffineGroupoid E) :
    H.symm.trans J ∈ piecewiseAffineGroupoid E := by
  letI := ChartedSpace.ofChartCover e hcover
  letI : HasGroupoid X (piecewiseAffineGroupoid E) :=
    ChartedSpace.hasGroupoid_ofChartCover e hcover (piecewiseAffineGroupoid E) hcompat
  have hmem (A : OpenPartialHomeomorph X E)
      (hA : ∀ i, (e i).symm.trans A ∈ piecewiseAffineGroupoid E) :
      A ∈ (piecewiseAffineGroupoid E).maximalAtlas X := by
    apply mem_maximalAtlas_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨by simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid E).symm (hA i), hA i⟩
  exact (piecewiseAffineGroupoid E).compatible_of_mem_maximalAtlas (hmem H hH) (hmem J hJ)

end Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_frontier_component_compatible_chart_labels
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {R C F T : Set X} (HC : (A.edgeComponentComplex c).space ≃ₜ T)
    (hTF : T ⊆ F) (hFU : F ⊆ R \ C)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    let charts := {H : OpenPartialHomeomorph X V3 |
      ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3}
    let q : charts → OpenPartialHomeomorph X V3 := Subtype.val
    let V : charts → Set (A.edgeComponentComplex c).space :=
      fun H => {z | (HC z : X) ∈ (q H).source}
    ∃ hq : ∀ H J, (q H).symm.trans (q J) ∈ piecewiseAffineGroupoid V3,
      ∃ label : ∀ H, LocallyConstant (V H) PLOrientationSheet,
        ∀ H J z (hH : z ∈ V H) (hJ : z ∈ V J),
          (label J ⟨z, hJ⟩).val =
            plAtlasTransitionSign q hq H J ⟨HC z, hH, hJ⟩ *
              (label H ⟨z, hH⟩).val := by
  let charts := {H : OpenPartialHomeomorph X V3 |
    ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3}
  let q : charts → OpenPartialHomeomorph X V3 := Subtype.val
  have hq : ∀ H J, (q H).symm.trans (q J) ∈ piecewiseAffineGroupoid V3 :=
    fun H J => compatiblePLCharts_trans e hcover hcompat H J H.property J.property
  have hqcover : ∀ x : X, ∃ H, x ∈ (q H).source := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨⟨e i, fun j => hcompat j i⟩, hi⟩
  obtain ⟨_, _, _, _, _, a0, L, _, _, _, _, label, _, hchange⟩ :=
    exists_original_frontier_component_sign_labels q hqcover hq A hA c HC hTF hFU hloops
  exact ⟨hq, label, hchange⟩

end PoincareConjecture.M76
