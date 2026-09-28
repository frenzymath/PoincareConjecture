import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CompactCapSide
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CanonicalCarrierUnion
import PoincareConjecture.Proofs.M28.Mathlib.FrontierCrossing

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CappedTubeCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

private theorem exists_side_of_first_cap_disjoint (T : CappedTubeCertificate g)
    (N₀ N₁ : EpsilonNeck g)
    (hS₀ : SmoothSphereIsotopicIn T.tube.carrier N₀.central_sphere T.tube.cylinder.middleSphere)
    (hS₁ : SmoothSphereIsotopicIn T.tube.carrier N₁.central_sphere T.tube.cylinder.middleSphere)
    (hdisj : Disjoint N₀.carrier N₁.carrier)
    (hcapN₀ : Disjoint T.cap.carrier N₀.carrier) :
    ∃ (k : Bool) (C : Set M), IsCompact C ∧ IsPreconnected C ∧ C ⊆ T.carrier ∧
      N₀.center ∈ C ∧ N₁.center ∈ C ∧
      (if k then N₁ else N₀).central_sphere ⊆ C ∧
      frontier C ⊆ (if k then N₁ else N₀).central_sphere := by
  obtain ⟨C₀, hC₀, hconn₀, hC₀U, hcap₀, hSC₀, hfront₀⟩ :=
    T.exists_preconnected_compact_cap_side hS₀ (hcapN₀.mono_right N₀.central_sphere_subset)
  have hcenter₀ : N₀.center ∈ C₀ := hSC₀ N₀.center_on_central_sphere
  by_cases hcenter₁ : N₁.center ∈ C₀
  · exact ⟨false, C₀, hC₀, hconn₀, hC₀U, hcenter₀, hcenter₁, hSC₀, hfront₀⟩
  · have hN₁C₀ : Disjoint N₁.carrier C₀ := by
      apply disjoint_left.mpr
      intro x hxN hxC
      obtain ⟨z, hzN, hzfront⟩ := N₁.isPreconnected_carrier.exists_mem_frontier_of_mem_of_notMem
        hxN hxC (N₁.central_sphere_subset N₁.center_on_central_sphere) hcenter₁
      exact disjoint_left.mp hdisj (N₀.central_sphere_subset (hfront₀ hzfront)) hzN
    have hcapN₁ : Disjoint T.cap.carrier N₁.carrier := by
      apply disjoint_left.mpr
      intro x hxcap hxN
      exact disjoint_left.mp hN₁C₀ hxN (interior_subset (hcap₀ hxcap))
    obtain ⟨C₁, hC₁, hconn₁, hC₁U, hcap₁, hSC₁, hfront₁⟩ :=
      T.exists_preconnected_compact_cap_side hS₁ (hcapN₁.mono_right N₁.central_sphere_subset)
    have hC₀C₁ : C₀ ⊆ C₁ := by
      intro x hx
      by_contra hxnot
      obtain ⟨p, hp⟩ := T.cap.core_nonempty
      have hpCap := T.cap.core_subset_carrier_m28 hp
      obtain ⟨z, hzC₀, hzfront⟩ := hconn₀.exists_mem_frontier_of_mem_of_notMem
        (interior_subset (hcap₀ hpCap)) (interior_subset (hcap₁ hpCap)) hx hxnot
      exact disjoint_left.mp hN₁C₀ (N₁.central_sphere_subset (hfront₁ hzfront)) hzC₀
    exact ⟨true, C₁, hC₁, hconn₁, hC₁U, hC₀C₁ hcenter₀,
      hSC₁ N₁.center_on_central_sphere, hSC₁, hfront₁⟩

theorem exists_compact_side_containing_chain_centers (T : CappedTubeCertificate g)
    (i j : ℤ) (hi : i ∈ T.tube.chain.shape.active) (hj : j ∈ T.tube.chain.shape.active)
    (hdisj : Disjoint (T.tube.chain.neck i).carrier (T.tube.chain.neck j).carrier)
    (hcap : Disjoint T.cap.carrier (T.tube.chain.neck i).carrier ∨
      Disjoint T.cap.carrier (T.tube.chain.neck j).carrier) :
    ∃ (k : Bool) (C : Set M), IsCompact C ∧ IsPreconnected C ∧ C ⊆ T.carrier ∧
      (T.tube.chain.neck i).center ∈ C ∧ (T.tube.chain.neck j).center ∈ C ∧
      (T.tube.chain.neck (if k then j else i)).central_sphere ⊆ C ∧
      frontier C ⊆ (T.tube.chain.neck (if k then j else i)).central_sphere := by
  rcases hcap with hcap | hcap
  · obtain ⟨k, C, hC, hconn, hCU, h₀, h₁, hS, hfront⟩ :=
      T.exists_side_of_first_cap_disjoint (T.tube.chain.neck i) (T.tube.chain.neck j)
        (T.tube.central_sphere_isotopy i hi) (T.tube.central_sphere_isotopy j hj) hdisj hcap
    refine ⟨k, C, hC, hconn, hCU, h₀, h₁, ?_, ?_⟩
    · cases k <;> exact hS
    · cases k <;> exact hfront
  · obtain ⟨k, C, hC, hconn, hCU, h₁, h₀, hS, hfront⟩ :=
      T.exists_side_of_first_cap_disjoint (T.tube.chain.neck j) (T.tube.chain.neck i)
        (T.tube.central_sphere_isotopy j hj) (T.tube.central_sphere_isotopy i hi) hdisj.symm hcap
    refine ⟨!k, C, hC, hconn, hCU, h₀, h₁, ?_, ?_⟩
    · cases k <;> exact hS
    · cases k <;> exact hfront

end PoincareConjecture.CappedTubeCertificate
