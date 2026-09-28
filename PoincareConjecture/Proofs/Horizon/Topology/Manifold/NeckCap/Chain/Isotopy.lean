import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Isotopy.Composition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.PairIsotopy

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_central_spheres_isotopic_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε),
        ε ≤ ε₀ → ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active,
          SmoothSphereIsotopicIn (C.unionOpen : Set M)
            (C.neck i).central_sphere (C.neck j).central_sphere := by
  obtain ⟨ε₀, hε₀, hsmall, hpair⟩ := EpsilonNeck.exists_two_neck_openCylinderModel.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε C hε
  have hsub (i : ℤ) (hi : i ∈ C.shape.active) :
      (C.neck i).carrier ⊆ (C.unionOpen : Set M) :=
    fun x hx => mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  have hadj (i : ℤ) (hi : i ∈ C.shape.active) (hi' : i + 1 ∈ C.shape.active) :
      SmoothSphereIsotopicIn (C.unionOpen : Set M)
        (C.neck i).central_sphere (C.neck (i + 1)).central_sphere := by
    have he := C.epsilon_eq i hi
    have he' := C.epsilon_eq (i + 1) hi'
    obtain ⟨_, hleft, hright⟩ := hpair (C.neck i) (C.neck (i + 1))
      (he.symm ▸ hε) (he'.symm ▸ hε)
      (by simpa only [he'] using (C.overlap_contains_quarters i hi hi').2)
      (by simpa only [he, he'] using C.overlap_within_three_quarters i hi hi')
    exact (hleft.trans hright.symm).mono (union_subset (hsub i hi) (hsub (i + 1) hi'))
  have hle (i j : ℤ) (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active) (hij : i ≤ j) :
      SmoothSphereIsotopicIn (C.unionOpen : Set M)
        (C.neck i).central_sphere (C.neck j).central_sphere := by
    have hn : ∀ n : ℕ, i + (n : ℤ) ∈ C.shape.active →
        SmoothSphereIsotopicIn (C.unionOpen : Set M)
          (C.neck i).central_sphere (C.neck (i + (n : ℤ))).central_sphere := by
      intro n
      induction n with
      | zero =>
        intro _
        simpa using ((C.neck i).central_sphere_isotopic_self).mono (hsub i hi)
      | succ n ih =>
        intro hn
        have hmid : i + (n : ℤ) ∈ C.shape.active :=
          C.shape.ordConnected_active.out hi hn ⟨by omega, by omega⟩
        have hnext : i + (n : ℤ) + 1 ∈ C.shape.active := by simpa [add_assoc] using hn
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          (ih hmid).trans (hadj (i + (n : ℤ)) hmid hnext)
    have heq : i + ((j - i).toNat : ℤ) = j := by omega
    simpa only [heq] using hn (j - i).toNat (heq.symm ▸ hj)
  intro i hi j hj
  obtain hij | hji := le_total i j
  · exact hle i j hi hj hij
  · exact (hle j i hj hi hji).symm

end PoincareConjecture.BalancedNeckChain
