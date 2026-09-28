import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalChartInwardPush
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalEdgeInwardDirection









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasOriginalEdgeCofaceCharts.exists_original_tetrahedron_inward_push
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {S : Set X} {K : SimplicialComplex ℝ E} {g : E → X} {p q : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p,q})
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hat : ({p,q} : Finset E) ⊆ t) {y : X}
    (hy : y ∈ S ∩ (g '' segment ℝ p q)) {O : Set X} (hO : IsOpen O) (hyO : y ∈ O) :
    ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ x, H x ∈ S ↔ x ∈ S) ∧
      (∀ x ∈ g '' convexHull ℝ (t : Set E),
        H x ∈ interior (g '' convexHull ℝ (t : Set E)) ∨ H x = x) ∧
      H y ∈ interior (g '' convexHull ℝ (t : Set E)) := by
  obtain ⟨B,V,F,A,w,hB,hyB,hV,hyV,hVT,hF,hS,hmap,hA,_,hw,hw0⟩ :=
    h.exists_tetrahedron_inward_direction hgi hSV hpq ht ht4 hat hy
  let L : V3 →ᵃ[ℝ] ℝ :=
    (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap.comp F.symm.toAffineEquiv.toAffineMap
  have hheight : L w = L (B y) := by
    change (F.symm w).2 = (F.symm (B y)).2
    rw [hw0,← hF,F.symm_apply_apply]
    rfl
  have hplane (z : V3) (hz : z ∈ V) : B.symm z ∈ S ↔ L z = 0 := by
    change B.symm z ∈ S ↔ (F.symm z).2 = 0
    simpa only [F.apply_symm_apply] using hS (F.symm z) (by simpa using hz)
  have hcarrier (z : V3) (hz : z ∈ V) :
      B.symm z ∈ g '' convexHull ℝ (t : Set E) ↔
        z ∈ A '' convexHull ℝ (t : Set E) := by
    constructor
    · rintro ⟨x,hx,hxz⟩
      refine ⟨x,hx,?_⟩
      rw [← hA hx,Function.comp_apply,hxz,B.right_inv (hVT hz)]
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x,hx,?_⟩
      rw [← hA hx,Function.comp_apply,B.left_inv (hmap hx)]
  have hyR : y ∈ g '' convexHull ℝ (t : Set E) := by
    apply image_mono (convexHull_mono (Finset.coe_subset.mpr hat))
    simpa only [Finset.coe_pair,convexHull_pair] using hy.2
  exact exists_original_chart_inward_push e he B hB hO hV hVT
    ((convex_convexHull ℝ _).affine_image A.toAffineMap) hcarrier L hplane
    hyB hyV hyR hyO hw hheight

end PoincareConjecture.M76
