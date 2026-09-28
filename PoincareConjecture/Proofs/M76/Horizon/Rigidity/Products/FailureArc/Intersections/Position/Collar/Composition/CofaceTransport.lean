import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasOriginalEdgeCofaceCharts.congr_on_open_edge_neighborhood
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    {S T U : Set X} {K : SimplicialComplex ℝ D} {g : D → X} {a : Finset D}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hU : IsOpen U) (hedge : g '' convexHull ℝ (a : Set D) ⊆ U)
    (hST : ∀ x ∈ U, x ∈ S ↔ x ∈ T) :
    HasOriginalEdgeCofaceCharts e T K g a := by
  intro y hy
  have hyU := hedge hy.2
  obtain ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, hFS, hFL, hcofaces⟩ :=
    h y ⟨(hST y hyU).mpr hy.1, hy.2⟩
  let W := V ∩ (B.target ∩ B.symm ⁻¹' U)
  refine ⟨B, W, F, hB, hyB,
    hV.inter (B.isOpen_inter_preimage_symm hU),
    ⟨hyV, B.map_source hyB, ?_⟩, (fun _ hz => hz.2.1), hF, ?_, ?_, hcofaces⟩
  · change B.symm (B y) ∈ U
    simpa only [B.left_inv hyB] using hyU
  · intro z hz
    exact (hST _ hz.2.2).symm.trans (hFS z hz.1)
  · intro z hz
    exact hFL z hz.1

theorem finite_contacts_and_coface_charts_congr_on_open
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    {S T U : Set X} {K : SimplicialComplex ℝ D} {g : D → X} {a : Finset D}
    (hfinite : (S ∩ (g '' convexHull ℝ (a : Set D))).Finite)
    (hcharts : HasOriginalEdgeCofaceCharts e S K g a)
    (hU : IsOpen U) (hedge : g '' convexHull ℝ (a : Set D) ⊆ U)
    (hST : ∀ x ∈ U, x ∈ S ↔ x ∈ T) :
    (T ∩ (g '' convexHull ℝ (a : Set D))).Finite ∧
      HasOriginalEdgeCofaceCharts e T K g a := by
  refine ⟨hfinite.subset ?_, hcharts.congr_on_open_edge_neighborhood hU hedge hST⟩
  intro y hy
  exact ⟨(hST y (hedge hy.2)).mpr hy.1, hy.2⟩

end PoincareConjecture.M76
