import PoincareConjecture.Proofs.M76.Wall.Mathlib.TriangleTreeSigns
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Sort










set_option autoImplicit false

namespace AbstractSimplicialComplex

theorem exists_numbered_triangle_enumeration
    {V : Type*} [DecidableEq V] (number : V ↪ ℕ) (s : Finset V) (hs : s.card = 3) :
    ∃ p : Fin 3 → V, Function.Injective p ∧ Finset.univ.image p = s ∧
      StrictMono (number ∘ p) := by
  let : LinearOrder V := LinearOrder.lift' number number.injective
  let p := s.orderEmbOfFin hs
  refine ⟨p, p.injective, ?_, ?_⟩
  · convert! s.image_orderEmbOfFin_univ hs
  · exact p.strictMono

theorem exists_triangle_edge_deleted_index
    {V : Type*} [DecidableEq V] (p : Fin 3 → V) (hp : Function.Injective p)
    (s t : Finset V) (ht : Finset.univ.image p = t) (hst : s ⊆ t) (hs : s.card = 2) :
    ∃ i : Fin 3, (Finset.univ.erase i).image p = s := by
  have htc : t.card = 3 := by
    rw [← ht, Finset.card_image_iff.mpr hp.injOn]
    rfl
  obtain ⟨v, hvs, hv⟩ := Finset.exists_eq_insert_iff.mpr ⟨hst, by omega⟩
  have hvt : v ∈ t := hv ▸ Finset.mem_insert_self v s
  rw [← ht] at hvt
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hvt
  refine ⟨i, ?_⟩
  rw [Finset.image_erase hp, ht, ← hv, Finset.erase_insert hvs]

theorem numbered_triangle_common_edge_order
    {V : Type*} [DecidableEq V] (number : V ↪ ℕ) (p q : Fin 3 → V)
    (hp : StrictMono (number ∘ p)) (hq : StrictMono (number ∘ q))
    (i j : Fin 3)
    (hedge : (Finset.univ.erase i).image p = (Finset.univ.erase j).image q) :
    p ∘ i.succAbove = q ∘ j.succAbove := by
  let : LinearOrder V := LinearOrder.lift' number number.injective
  have hpi : Function.Injective p := fun a b he => hp.injective (congrArg number he)
  let e := (Finset.univ.erase i).image p
  have hecard : e.card = 2 := by
    dsimp only [e]
    rw [Finset.card_image_iff.mpr hpi.injOn]
    simp
  have hpMem (k : Fin 2) : p (i.succAbove k) ∈ e := by
    exact Finset.mem_image.mpr ⟨i.succAbove k,
      Finset.mem_erase.mpr ⟨Fin.succAbove_ne i k, Finset.mem_univ _⟩, rfl⟩
  have hqMem (k : Fin 2) : q (j.succAbove k) ∈ e := by
    change q (j.succAbove k) ∈ (Finset.univ.erase i).image p
    rw [hedge]
    exact Finset.mem_image.mpr ⟨j.succAbove k,
      Finset.mem_erase.mpr ⟨Fin.succAbove_ne j k, Finset.mem_univ _⟩, rfl⟩
  have hpm : StrictMono (p ∘ i.succAbove) := hp.comp (Fin.strictMono_succAbove i)
  have hqm : StrictMono (q ∘ j.succAbove) := hq.comp (Fin.strictMono_succAbove j)
  exact (Finset.orderEmbOfFin_unique hecard hpMem hpm).trans
    (Finset.orderEmbOfFin_unique hecard hqMem hqm).symm

theorem boundaryFaceParity_ordered_triangle
    {V : Type*} [DecidableEq V] (number : V → ℕ) (p : Fin 3 → V)
    (hp : Function.Injective p) (hnumber : StrictMono (number ∘ p)) (i : Fin 3) :
    boundaryFaceParity number (Finset.univ.image p) ((Finset.univ.erase i).image p) =
      (i.val : ZMod 2) := by
  have hdiff : Finset.univ.image p \ (Finset.univ.erase i).image p = {p i} := by
    rw [← Finset.image_sdiff _ _ hp]
    have he : (Finset.univ : Finset (Fin 3)) \ Finset.univ.erase i = {i} := by
      ext j
      simp
    rw [he, Finset.image_singleton]
  have hfilter : (Finset.univ.image p).filter (fun w => number w < number (p i)) =
      (Finset.Iio i).image p := by
    rw [Finset.filter_image]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact hnumber.lt_iff_lt
  simp only [boundaryFaceParity, hdiff, Finset.sum_singleton, hfilter]
  rw [Finset.card_image_iff.mpr hp.injOn, Fin.card_Iio]

end AbstractSimplicialComplex
