import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapProductGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeEndpointCenteredCut

set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Base" => frontier (halfBall 1)
local notation "I" => Icc (0 : ℝ) 1

theorem ChartwisePLSphere.exists_original_product_endpoint_relative_noL3_cut
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R U S V : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (W : U ≃ₜ (Base ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (Base ×ˢ I))
    (hσval : ∀ z : (Base ×ˢ I : Set (P3 × ℝ)), σ z = (W.symm z : X))
    (b : Bool) (hSU : S ⊆ U) (hUR : U ⊆ interior R)
    (hmark : ∀ x : U, (x : X) ∈ S ↔
      (W x : P3 × ℝ).2 = if b then (1 : ℝ) else 0)
    (hV : IsOpen V) (hSV : S ⊆ V)
    (hno : HasNoPuncturedSphereComponents e f (R \ interior U))
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    ∃ (c : V3 × ℝ → X) (ε : ℝ),
      PolyhedralPLInCharts e c (Sphere ×ˢ Icc (-1 : ℝ) 1) ∧
      InjOn c (Sphere ×ˢ Icc (-1 : ℝ) 1) ∧
      (∀ x ∈ Sphere, c (x,0) = s.map x) ∧
      0 < ε ∧ ε ≤ 1 / 24 ∧
      MapsTo c (Sphere ×ˢ Icc (-ε) ε) (V ∩ interior R) ∧
      (∀ η : ℝ, 0 < η → η ≤ ε → IsOpen (c '' (Sphere ×ˢ Ioo (-η) η))) ∧
      HasNoPuncturedSphereComponents e f (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) ∧
      ∃ (D : Bool → Set X) (_sD : ∀ i, ChartwisePLSphere e (D i))
        (H : (Sphere × unitInterval) ≃ₜ closure (c '' (Sphere ×ˢ Ioo (-ε) ε))),
        IsCompact (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) ∧
        PLDomain e (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) ∧
        Pairwise (fun i j => Disjoint (D i) (D j)) ∧
        (∀ i, D i ⊆ closure (c '' (Sphere ×ˢ Ioo (-ε) ε))) ∧
        frontier (c '' (Sphere ×ˢ Ioo (-ε) ε)) = D false ∪ D true ∧
        frontier (R \ c '' (Sphere ×ˢ Ioo (-ε) ε)) = frontier R ∪ ⋃ i, D i ∧
        closure (c '' (Sphere ×ˢ Ioo (-ε) ε)) ⊆ interior R ∧
        (∀ z, (H z : X) ∈ c '' (Sphere ×ˢ Ioo (-ε) ε) ↔
          (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ z, (H z : X) ∈ S ↔ (z.2 : ℝ) = 1 / 2) ∧
        S ⊆ closure (c '' (Sphere ×ˢ Ioo (-ε) ε)) := by
  obtain ⟨hUc,T,sT,hfrontU,hST⟩ :=
    original_selected_product_endpoint_geometry W σ hσ hσval b hSU hmark
  have hUPL := original_sphere_product_plDomain W σ hσ hσval he.compatible he.cover
  exact s.exists_selected_endpoint_relative_centered_noL3_cut sT hR he hUPL hUc hUR
    hfrontU hST hV hSV hno L g hf hg hgi hreal

end PoincareConjecture.M76
