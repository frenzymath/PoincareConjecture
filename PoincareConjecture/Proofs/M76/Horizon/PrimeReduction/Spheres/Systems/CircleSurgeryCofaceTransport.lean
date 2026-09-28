import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HasOriginalEdgeCofaceCharts.surgery_left_of_disjoint_support
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S S₀ S₁ C : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hC : IsClosed C) (hother : IsClosed S₁) (hdis : Disjoint S₀ S₁)
    (hCedge : Disjoint C (g '' convexHull ℝ (a : Set E)))
    (houtside : (S₀ ∪ S₁) \ C = S \ C) :
    HasOriginalEdgeCofaceCharts e S₀ K g a := by
  have hmem {x : X} (hxC : x ∉ C) (hxother : x ∉ S₁) :
      x ∈ S₀ ↔ x ∈ S := by
    have hx := Set.ext_iff.mp houtside x
    simpa only [mem_sdiff, mem_union, hxC, hxother, or_false, not_false_eq_true,
      and_true] using hx
  intro y hy
  have hyC : y ∉ C := fun hc => disjoint_left.mp hCedge hc hy.2
  have hyother : y ∉ S₁ := disjoint_left.mp hdis hy.1
  obtain ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, hFS, hFL, hcofaces⟩ :=
    h y ⟨(hmem hyC hyother).mp hy.1, hy.2⟩
  let U := Cᶜ ∩ S₁ᶜ
  have hU : IsOpen U := hC.isOpen_compl.inter hother.isOpen_compl
  let W := V ∩ (B.target ∩ B.symm ⁻¹' U)
  refine ⟨B, W, F, hB, hyB,
    hV.inter (B.isOpen_inter_preimage_symm hU),
    ⟨hyV, B.mapsTo hyB, ?_⟩, (fun _ hz => hz.2.1), hF, ?_, ?_, hcofaces⟩
  · change B.symm (B y) ∈ U
    simpa only [B.left_inv hyB] using (show y ∈ U from ⟨hyC, hyother⟩)
  · intro z hz
    exact (hmem hz.2.2.1 hz.2.2.2).trans (hFS z hz.1)
  · intro z hz
    exact hFL z hz.1

theorem HasOriginalEdgeCofaceCharts.surgery_pair_of_disjoint_support
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S S₀ S₁ C : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hC : IsClosed C) (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁)
    (hdis : Disjoint S₀ S₁)
    (hCedge : Disjoint C (g '' convexHull ℝ (a : Set E)))
    (houtside : (S₀ ∪ S₁) \ C = S \ C) :
    HasOriginalEdgeCofaceCharts e S₀ K g a ∧
      HasOriginalEdgeCofaceCharts e S₁ K g a := by
  refine ⟨h.surgery_left_of_disjoint_support hC hS₁.isClosed hdis hCedge houtside,
    h.surgery_left_of_disjoint_support hC hS₀.isClosed hdis.symm hCedge ?_⟩
  simpa only [union_comm S₁ S₀] using houtside

end PoincareConjecture.M76
