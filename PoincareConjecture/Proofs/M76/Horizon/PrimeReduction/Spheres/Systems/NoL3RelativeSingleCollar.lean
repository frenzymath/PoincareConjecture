import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeComponentSubregions
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawSphereCutComponents









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.mono_relative_single_collar
    {X E A₀ A₁ ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace A₀] [TopologicalSpace A₁]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    (R S O₀ O₁ : Set X)
    (W₀ : (A₀ × unitInterval) ≃ₜ closure O₀)
    (W₁ : (A₁ × unitInterval) ≃ₜ closure O₁)
    (hQ₀ : IsCompact (R \ O₀)) (hQ₀PL : PLDomain e (R \ O₀))
    (hQ₁ : IsCompact (R \ O₁)) (hQ₁PL : PLDomain e (R \ O₁))
    (hCR₀ : closure O₀ ⊆ interior R) (hCR₁ : closure O₁ ⊆ interior R)
    (hO₀ : ∀ z, (W₀ z : X) ∈ O₀ ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hO₁ : ∀ z, (W₁ z : X) ∈ O₁ ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS₀ : ∀ z, (W₀ z : X) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (hS₁ : ∀ z, (W₁ z : X) ∈ S ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : S ⊆ closure O₀) (hSC₁ : S ⊆ closure O₁) (hnest : O₁ ⊆ O₀)
    (B₀ B₁ : Bool → Set X)
    (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i)) (sB₁ : ∀ i, ChartwisePLSphere e (B₁ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure O₀) (hB₁sub : ∀ i, B₁ i ⊆ closure O₁)
    (hfront₀ : frontier (R \ O₀) = frontier R ∪ ⋃ i, B₀ i)
    (hfront₁ : frontier (R \ O₁) = frontier R ∪ ⋃ i, B₁ i)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f (R \ O₀)) :
    HasNoPuncturedSphereComponents e f (R \ O₁) := by
  have hdis (O : Set X) : Pairwise fun (_i _j : Unit) => Disjoint (closure O) (closure O) := by
    intro i j hij
    exact False.elim (hij (Subsingleton.elim _ _))
  obtain ⟨r,_,hrQ,_,hrcc,_⟩ := exists_raw_sphere_cut_component_map
    R (R \ O₀) (fun (_ : Unit) => O₀) (fun (_ : Unit) => S) (fun _ => W₀)
    (congrArg (fun T => R \ T) (iUnion_const (ι := Unit) O₀).symm)
    hQ₀.isClosed (fun _ => hCR₀.trans interior_subset) (hdis O₀)
    (fun _ => hO₀) (fun _ => hS₀) (fun _ => hSC₀)
  obtain ⟨_,_,_,_,_,hcomp,_⟩ := exists_raw_sphere_cut_component_map
    R (R \ O₁) (fun (_ : Unit) => O₁) (fun (_ : Unit) => S) (fun _ => W₁)
    (congrArg (fun T => R \ T) (iUnion_const (ι := Unit) O₁).symm)
    hQ₁.isClosed (fun _ => hCR₁.trans interior_subset) (hdis O₁)
    (fun _ => hO₁) (fun _ => hS₁) (fun _ => hSC₁)
  have hF₀ : Disjoint (frontier R) (⋃ i, B₀ i) := by
    apply disjoint_left.mpr
    intro x hx hb
    obtain ⟨i,hi⟩ := mem_iUnion.mp hb
    exact hx.2 (hCR₀ (hB₀sub i hi))
  have hF₁ : Disjoint (frontier R) (⋃ i, B₁ i) := by
    apply disjoint_left.mpr
    intro x hx hb
    obtain ⟨i,hi⟩ := mem_iUnion.mp hb
    exact hx.2 (hCR₁ (hB₁sub i hi))
  intro x hx hm
  have hxraw : x ∈ R \ ⋃ (_ : Unit), S := by
    have hh := mem_connectedComponentIn hx
    rw [hcomp x hx] at hh
    exact connectedComponentIn_subset _ _ hh.1
  have hy := hrQ hxraw
  have hQnest : R \ O₀ ⊆ R \ O₁ := sdiff_subset_sdiff_right hnest
  have hynew : r x ∈ connectedComponentIn (R \ O₁) x := by
    rw [hcomp x hx]
    exact ⟨hrcc x hxraw,hQnest hy⟩
  exact hno (r x) hy (hm.of_original_relative_cut_component hQ₀ hQ₀PL hQ₁ hQ₁PL
    hQnest isClosed_frontier B₀ sB₀ hB₀dis hF₀ hfront₀ B₁ sB₁ hF₁ hfront₁
    L g hg hgi (fun z hz => hreal z hz.1) hx hy hynew)

end PoincareConjecture.M76
