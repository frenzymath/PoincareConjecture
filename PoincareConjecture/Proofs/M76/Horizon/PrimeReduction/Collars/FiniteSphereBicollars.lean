import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalSphereBicollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import Mathlib.Order.Filter.Bases.Finite










set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_disjoint_open_sphere_neighborhoods
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} (S : κ → Set X)
    (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ O : κ → Set X, (∀ i, IsOpen (O i) ∧ S i ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (O i) (O j)) := by
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (S i)) (𝓝ˢ (S j))) := by
    intro i j hij
    exact (SeparatedNhds.of_isCompact_isCompact (sS i).isCompact
      (sS j).isCompact (hdis hij)).disjoint_nhdsSet
  exact hd.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (S i))

theorem exists_original_finite_sphere_bicollars_with_model
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (t : κ → Finset R) (F : ∀ i, X → (t i → ℝ × V3))
      (N : ∀ i, SimplicialComplex ℝ (t i → ℝ × V3))
      (HB : ∀ i, (N i).space ≃ₜ S i)
      (c : ∀ i, (t i → ℝ × V3) × ℝ → X) (δ : κ → ℝ),
      (∀ i, Continuous (F i) ∧
        (∀ j, LocallyPiecewiseAffineOn (F i ∘ (e j).symm) (e j).target) ∧
        InjOn (F i) R ∧ (N i).space = F i '' S i) ∧
      (∀ i, (N i).faces.Finite ∧
        PolyhedralPLInCharts e (c i) ((N i).space ×ˢ J) ∧
        Topology.IsEmbedding (fun z : ((N i).space ×ˢ J :
          Set ((t i → ℝ × V3) × ℝ)) => c i z) ∧
        MapsTo (c i) ((N i).space ×ˢ J) R ∧
        (∀ x : (N i).space, c i ((x : t i → ℝ × V3), 0) = HB i x) ∧
        (∀ z : ((N i).space ×ˢ J : Set ((t i → ℝ × V3) × ℝ)),
          c i z ∈ S i ↔ (z : (t i → ℝ × V3) × ℝ).2 = 0) ∧
        0 < δ i ∧ δ i ≤ 1 / 2 ∧
        MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i)) (U ∩ interior R) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ i →
          IsOpen (c i '' ((N i).space ×ˢ Ioo (-ε) ε))) ∧
      Pairwise (fun i j =>
        Disjoint (c i '' ((N i).space ×ˢ Icc (-δ i) (δ i)))
          (c j '' ((N j).space ×ˢ Icc (-δ j) (δ j)))) := by
  classical
  obtain ⟨O, hO, hOd⟩ := exists_disjoint_open_sphere_neighborhoods S sS hdis
  have hall (i : κ) := (sS i).exists_original_small_bicollar_with_model hR he (hSR i)
    ((hO i).1.inter hU) (fun x hx => ⟨(hO i).2 hx, hSU i hx⟩)
  choose t F N HB c hFc hF hFi hNs hN hPL hc hcR hc0 hcz δ hδ hδsmall hinside hopen using hall
  refine ⟨t, F, N, HB, c, δ, fun i => ⟨hFc i, hF i, hFi i, hNs i⟩, ?_, ?_⟩
  · intro i
    exact ⟨hN i, hPL i, hc i, hcR i, hc0 i, hcz i, hδ i, hδsmall i,
      fun _ hz => ⟨(hinside i hz).1.2, (hinside i hz).2⟩, hopen i⟩
  · intro i j hij
    apply (hOd hij).mono
    · rintro _ ⟨z, hz, rfl⟩
      exact (hinside i hz).1.1
    · rintro _ ⟨z, hz, rfl⟩
      exact (hinside j hz).1.1

theorem exists_original_finite_sphere_bicollars
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (t : κ → Finset R)
      (N : ∀ i, SimplicialComplex ℝ (t i → ℝ × V3))
      (HB : ∀ i, (N i).space ≃ₜ S i)
      (c : ∀ i, (t i → ℝ × V3) × ℝ → X) (δ : κ → ℝ),
      (∀ i, (N i).faces.Finite ∧
        PolyhedralPLInCharts e (c i) ((N i).space ×ˢ J) ∧
        Topology.IsEmbedding (fun z : ((N i).space ×ˢ J :
          Set ((t i → ℝ × V3) × ℝ)) => c i z) ∧
        MapsTo (c i) ((N i).space ×ˢ J) R ∧
        (∀ x : (N i).space, c i ((x : t i → ℝ × V3), 0) = HB i x) ∧
        (∀ z : ((N i).space ×ˢ J : Set ((t i → ℝ × V3) × ℝ)),
          c i z ∈ S i ↔ (z : (t i → ℝ × V3) × ℝ).2 = 0) ∧
        0 < δ i ∧ δ i ≤ 1 / 2 ∧
        MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i)) (U ∩ interior R) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ i →
          IsOpen (c i '' ((N i).space ×ˢ Ioo (-ε) ε))) ∧
      Pairwise (fun i j =>
        Disjoint (c i '' ((N i).space ×ˢ Icc (-δ i) (δ i)))
          (c j '' ((N j).space ×ˢ Icc (-δ j) (δ j)))) := by
  obtain ⟨t, _, N, HB, c, δ, _, hdata⟩ :=
    exists_original_finite_sphere_bicollars_with_model S sS hdis hR he hSR hU hSU
  exact ⟨t, N, HB, c, δ, hdata⟩

end PoincareConjecture.M76
