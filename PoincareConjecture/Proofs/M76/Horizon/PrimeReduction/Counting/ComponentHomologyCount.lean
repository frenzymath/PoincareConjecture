import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FiniteComponentHomology









set_option autoImplicit false
open Set CategoryTheory Limits
open scoped BigOperators

universe u v
namespace PoincareConjecture.M76

theorem PLDomain.card_le_zero_homology_components_add_rank_sum
    {X V : Type u} {ι : Type v} [TopologicalSpace X] [T2Space X] [Fintype V]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (D : V → Set X) (hD : ∀ v, IsCompact (D v))
    (hPL : ∀ v, PLDomain e (D v)) (n : ℕ) :
    Fintype.card V ≤ {v | IsZero (ModTwoMayerVietoris.homology (D v) n)}.ncard +
      ∑ v, Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology (D v) n) := by
  classical
  let : ∀ v, Module.Finite (ZMod 2) (ModTwoMayerVietoris.homology (D v) n) :=
    fun v => (hPL v).finite_modTwo_homology (hD v) n
  have hpoint (v : V) : 1 ≤
      (if IsZero (ModTwoMayerVietoris.homology (D v) n) then 1 else 0) +
        Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology (D v) n) := by
    split_ifs with hz
    · omega
    · have hpos : 0 < Module.finrank (ZMod 2)
          (ModTwoMayerVietoris.homology (D v) n) := by
        apply Nat.pos_of_ne_zero
        intro hzero
        exact hz (ModuleCat.isZero_iff_subsingleton.mpr
          (Module.finrank_zero_iff.mp hzero))
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  simpa [Finset.sum_add_distrib, Set.ncard_eq_toFinset_card'] using hsum

theorem PLDomain.card_le_zero_homology_components_add_finrank
    {X V : Type u} {ι : Type v} [TopologicalSpace X] [T2Space X] [Fintype V]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (Q : Set X) (D : V → Set X) (hD : ∀ v, IsCompact (D v))
    (hPL : ∀ v, PLDomain e (D v))
    (hdis : Pairwise fun v w => Disjoint (D v) (D w)) (hcover : (⋃ v, D v) = Q)
    (n : ℕ) :
    Fintype.card V ≤ {v | IsZero (ModTwoMayerVietoris.homology (D v) n)}.ncard +
      Module.finrank (ZMod 2) (ModTwoMayerVietoris.homology Q n) := by
  rw [PLDomain.finrank_disjoint_components Q D hD hPL hdis hcover n]
  exact PLDomain.card_le_zero_homology_components_add_rank_sum D hD hPL n

end PoincareConjecture.M76
