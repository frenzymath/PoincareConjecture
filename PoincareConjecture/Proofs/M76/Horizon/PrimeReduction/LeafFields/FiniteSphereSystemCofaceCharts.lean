import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem hasOriginalEdgeCofaceCharts_finite_sphere_system
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (K : SimplicialComplex ℝ E) (g : E → X) (a : Finset E)
    (hcharts : ∀ i, HasOriginalEdgeCofaceCharts e (S i) K g a) :
    HasOriginalEdgeCofaceCharts e (⋃ i, S i) K g a := by
  intro y hy
  obtain ⟨i, hyi⟩ := mem_iUnion.mp hy.1
  obtain ⟨O, hO, hSiO, hOi, _⟩ := exists_open_sphere_system_isolation S sS hdis i
  obtain ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, hFS, hFL, hcofaces⟩ :=
    hcharts i y ⟨hyi, hy.2⟩
  let W := V ∩ (B.target ∩ B.symm ⁻¹' O)
  refine ⟨B, W, F, hB, hyB, hV.inter (B.isOpen_inter_preimage_symm hO),
    ⟨hyV, B.map_source hyB, ?_⟩, (fun z hz => hVB hz.1), hF, ?_, ?_, hcofaces⟩
  · simpa only [mem_preimage, B.left_inv hyB] using hSiO hyi
  · intro z hz
    have hmem : B.symm (F z) ∈ ⋃ j, S j ↔ B.symm (F z) ∈ S i := by
      constructor
      · intro h
        exact hOi.subset ⟨hz.2.2, h⟩
      · exact fun h => mem_iUnion.mpr ⟨i, h⟩
    exact hmem.trans (hFS z hz.1)
  · intro z hz
    exact hFL z hz.1

theorem HasOriginalEdgeCofaceCharts.of_finite_sphere_system
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    {K : SimplicialComplex ℝ E} {g : E → X} {a : Finset E}
    (hcharts : HasOriginalEdgeCofaceCharts e (⋃ i, S i) K g a) (i : κ) :
    HasOriginalEdgeCofaceCharts e (S i) K g a := by
  intro y hy
  obtain ⟨O, hO, hSiO, hOi, _⟩ := exists_open_sphere_system_isolation S sS hdis i
  obtain ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, hFS, hFL, hcofaces⟩ :=
    hcharts y ⟨mem_iUnion.mpr ⟨i, hy.1⟩, hy.2⟩
  let W := V ∩ (B.target ∩ B.symm ⁻¹' O)
  refine ⟨B, W, F, hB, hyB, hV.inter (B.isOpen_inter_preimage_symm hO),
    ⟨hyV, B.map_source hyB, ?_⟩, (fun z hz => hVB hz.1), hF, ?_, ?_, hcofaces⟩
  · simpa only [mem_preimage, B.left_inv hyB] using hSiO hy.1
  · intro z hz
    have hmem : B.symm (F z) ∈ S i ↔ B.symm (F z) ∈ ⋃ j, S j := by
      constructor
      · exact fun h => mem_iUnion.mpr ⟨i, h⟩
      · intro h
        exact hOi.subset ⟨hz.2.2, h⟩
    exact hmem.trans (hFS z hz.1)
  · intro z hz
    exact hFL z hz.1

theorem finite_edge_contacts_of_finite_sphere_system
    {X κ : Type*} [Finite κ] (S : κ → Set X) (edge : Set X)
    (hfinite : ∀ i, (S i ∩ edge).Finite) : ((⋃ i, S i) ∩ edge).Finite := by
  rw [iUnion_inter]
  exact finite_iUnion hfinite

end PoincareConjecture.M76
