import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CompactDeck.Homology
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CompactDeck.HurewiczAction
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.HomologyTrace












set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable (P02 : RepairedClosedTopologyProvider.{u})
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [SimplyConnectedSpace M]

include P02



theorem compactThree_homology_trace_sum (f : C(M, M)) (N : ℕ) (hN : 3 ≤ N) :
    (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
      LinearMap.trace ℤ (integralHomology M i)
        (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) i).hom) =
      1 - LinearMap.trace ℤ (integralHomology M 3)
        (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) 3).hom := by
  classical
  let T (i : ℕ) := LinearMap.trace ℤ (integralHomology M i)
    (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) i).hom
  have ht (i : ℕ) : (-1 : ℤ) ^ i * T i =
      (if i = 0 then 1 else 0) + (if i = 3 then -T 3 else 0) := by
    by_cases hi : i = 0
    · subst i
      simp [T, trace_integralHomologyMap_zero]
    by_cases hi3 : i = 3
    · subst i
      norm_num
    · have hz := compactThree_integralHomology_isZero P02 (M := M) i hi hi3
      have hm : homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) i = 0 :=
        hz.eq_of_tgt _ _
      simp only [T, hm, ModuleCat.hom_zero, map_zero, mul_zero, hi, hi3,
        ↓reduceIte, add_zero]
  change (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * T i) = 1 - T 3
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_add_one_iff,
    Nat.zero_le, hN, ↓reduceIte, sub_eq_add_neg]




theorem compactThree_homologyMap_eq_id_of_finite_model
    (f : C(M, M)) (C : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    [∀ i, Module.Free ℤ (C.X i)] [∀ i, Module.Finite ℤ (C.X i)]
    (F : C ⟶ C) (e : ∀ i, C.homology i ≅ integralHomology M i)
    (he : ∀ i, homologyMap F i ≫ (e i).hom = (e i).hom ≫
      homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) i)
    (N : ℕ) (hN : 3 ≤ N) (htop : C.d (N + 1) N = 0)
    (htrace : C.alternatingTrace F N = 0) :
    surgeryThirdHomologyMap f = LinearMap.id := by
  let hfree (i : ℕ) := compactThree_integralHomology_free P02 (M := M) i
  let hfinite (i : ℕ) := compactThree_integralHomology_finite P02 (M := M) i
  let hCfree (i : ℕ) := Module.Free.of_equiv (e i).toLinearEquiv.symm
  let hCfinite (i : ℕ) := ChainComplex.moduleFinite_homology (C := C) i
  have hsum := ChainComplex.alternatingTrace_eq_homology_sum F N htop
  have heq (i : ℕ) := ModuleCat.trace_eq_of_iso (e i) (homologyMap F i)
    (homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) i) (he i)
  simp_rw [heq] at hsum
  rw [compactThree_homology_trace_sum P02 f N hN, htrace] at hsum
  apply compactThree_homologyMap_eq_id_of_trace_one f
  exact (sub_eq_zero.mp hsum.symm).symm



theorem compactThree_homologyMap_eq_id_of_zero_diagonal_model
    (f : C(M, M)) (C : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    [∀ i, Module.Free ℤ (C.X i)] [∀ i, Module.Finite ℤ (C.X i)]
    (F : C ⟶ C) (e : ∀ i, C.homology i ≅ integralHomology M i)
    (he : ∀ i, homologyMap F i ≫ (e i).hom = (e i).hom ≫
      homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) i)
    (N : ℕ) (hN : 3 ≤ N) (htop : C.d (N + 1) N = 0)
    (ι : ℕ → Type u) [∀ i, Finite (ι i)] (b : ∀ i, Module.Basis (ι i) ℤ (C.X i))
    (hdiag : ∀ i ≤ N, ∀ j, (b i).repr ((F.f i).hom (b i j)) j = 0) :
    surgeryThirdHomologyMap f = LinearMap.id := by
  apply compactThree_homologyMap_eq_id_of_finite_model P02 f C F e he N hN htop
  exact ChainComplex.alternatingTrace_eq_zero_of_diagonal_eq_zero F N ι b hdiag




theorem compactThree_piThreeMap_eq_transport_of_zero_diagonal_model
    (f : C(M, M)) (x : M) (p : Path x (f x))
    (C : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    [∀ i, Module.Free ℤ (C.X i)] [∀ i, Module.Finite ℤ (C.X i)]
    (F : C ⟶ C) (e : ∀ i, C.homology i ≅ integralHomology M i)
    (he : ∀ i, homologyMap F i ≫ (e i).hom = (e i).hom ≫
      homologyMap (integralChainsFunctor.map (TopCat.ofHom f)) i)
    (N : ℕ) (hN : 3 ≤ N) (htop : C.d (N + 1) N = 0)
    (ι : ℕ → Type u) [∀ i, Finite (ι i)] (b : ∀ i, Module.Basis (ι i) ℤ (C.X i))
    (hdiag : ∀ i ≤ N, ∀ j, (b i).repr ((F.f i).hom (b i j)) j = 0)
    (a : HomotopyGroup.Pi 3 M x) :
    surgeryHomotopyMap (n := 3) f rfl a =
      (m59HigherBasepointTransport M 3).map p a := by
  exact compactThree_piThreeMap_eq_transport_of_homologyMap_eq_id P02 f x p
    (compactThree_homologyMap_eq_id_of_zero_diagonal_model
      P02 f C F e he N hN htop ι b hdiag) a

end PoincareConjecture.Proofs.M59
