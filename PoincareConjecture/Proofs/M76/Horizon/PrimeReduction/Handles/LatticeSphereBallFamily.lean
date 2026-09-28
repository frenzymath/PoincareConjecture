import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LatticeSphereDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.QuotientRegionNesting
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.OutermostSphereBalls

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_outermost_lattice_sphere_balls
    {ι κ α ν : Type*} [Fintype ι] [Fintype κ] [Finite ν]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (S : ν → Set (LatticeHandleAmbient ι κ L))
    (s : ∀ i, ChartwisePLSphere e (S i))
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : ∀ i, S i ⊆ interior (latticeHandleDomain ι κ L))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∃ Q : ν → Set (LatticeHandleAmbient ι κ L),
      (∀ i, IsCompact (Q i)) ∧ (∀ i, frontier (Q i) = S i) ∧
      (∀ i, IsUnitBallPair V3 (Q i) (S i)) ∧
      (∀ i, PLDomain e (Q i)) ∧
      (∀ i, Q i ⊆ interior (latticeHandleDomain ι κ L)) ∧
      (∀ i j, Disjoint (Q i) (Q j) ∨ Q i ⊆ Q j ∨ Q j ⊆ Q i) ∧
      ∃ t : Finset ν, Pairwise (fun i j : t => Disjoint (Q i) (Q j)) ∧
        (∀ i, ∃ j : t, Q i ⊆ Q j) ∧
        (⋃ j : t, Q j) = ⋃ i, Q i ∧
        (⋃ j : t, interior (Q j)) = ⋃ i, interior (Q i) ∧
        ∀ i, i ∉ t → ∃ j : t, Q i ⊆ interior (Q j) := by
  classical
  choose Q hQ hfront hball hinside U hU hUc hcompact hUf hQeq hSeq using
    fun i => (s i).exists_lattice_ball_pair_with_lift L he hdim (hSR i)
  let V := (ι → ℝ) × (κ → ℝ)
  have hdimV : Module.finrank ℝ V = 3 := by
    simpa only [V,Module.finrank_prod,Module.finrank_pi,Module.finrank_self,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hdim
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [hdimV]
    norm_num)
  let p : V →+ LatticeHandleAmbient ι κ L :=
    (AddMonoidHom.id (ι → ℝ)).prodMap (QuotientAddGroup.mk' L.toAddSubgroup)
  have hQp (i : ν) : Q i = p '' closure (U i) := hQeq i
  have hSp (i : ν) : S i = p '' frontier (U i) := hSeq i
  have hnested (i j : ν) : Disjoint (Q i) (Q j) ∨ Q i ⊆ Q j ∨ Q j ⊆ Q i := by
    by_cases hij : i = j
    · exact Or.inr (Or.inl (hij ▸ subset_rfl))
    have hdis' : Disjoint (p '' frontier (U i)) (p '' frontier (U j)) := by
      rw [← hSp i,← hSp j]
      exact hdis hij
    have h := disjoint_or_nested_projected_bounded_regions p (hU i) (hU j)
      ((hcompact i).isBounded.subset subset_closure)
      ((hcompact j).isBounded.subset subset_closure) (hUc i) (hUc j) (hUf i) (hUf j) hdis'
    rwa [← hQp i,← hQp j] at h
  have hfrontNonempty (i : ν) : (frontier (Q i)).Nonempty := by
    rw [hfront i]
    obtain ⟨x,hx⟩ := NormedSpace.sphere_nonempty (E := V3) (x := 0) |>.mpr
      (show (0 : ℝ) ≤ 1 by norm_num)
    exact ⟨(s i).parametrization ⟨x,hx⟩,((s i).parametrization ⟨x,hx⟩).property⟩
  have hfrontDis : Pairwise fun i j => Disjoint (frontier (Q i)) (frontier (Q j)) := by
    simpa only [hfront] using hdis
  refine ⟨Q,hQ,hfront,hball,?_,hinside,hnested,?_⟩
  · intro i
    exact (s i).plDomain_of_unitBallPair (hQ i) (hfront i) (hball i) he.compatible he.cover
  · exact exists_outermost_sphere_ball_subfamily Q hfrontNonempty hfrontDis hnested

end PoincareConjecture.M76
