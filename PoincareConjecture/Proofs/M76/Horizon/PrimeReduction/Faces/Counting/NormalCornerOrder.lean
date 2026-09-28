import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Counting.CornerOrder
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.CornerComponentTransport

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem exists_normal_corner_order
    {ι : Type*} [Finite ι] (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hD : ∀ k, IsFinitePLBallPair ℝ (D k) {p k, q k})
    (hrim : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) = D k ∩ frontier base)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hpv : ∀ k, p k ∉ vertices) (hqv : ∀ k, q k ∉ vertices)
    (hleft : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (hdiagonal : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {x ∈ base | x.1 + x.2 = 1}) :
    ∃ (c : ι → Fin 3) (a b : ι → ℝ),
      (∀ i, a i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i, b i ∈ Ioo (0 : ℝ) 1) ∧
      (∀ i, cornerMap (c i) '' ({p i, q i} : Set (ℝ × ℝ)) = {(0, b i), (a i, 0)}) ∧
      (∀ i j, c i = c j → a i = a j → i = j) ∧
      Nat.card {i : ι // ∃ j, c j = c i ∧ a i < a j} + Nat.card (range c) = Nat.card ι ∧
      Nat.card (range c) ≤ 3 := by
  classical
  have hex (i : ι) : ∃ c : Fin 3, ∃ a ∈ Ioo (0 : ℝ) 1, ∃ b ∈ Ioo (0 : ℝ) 1,
      cornerMap c '' ({p i, q i} : Set (ℝ × ℝ)) = {(0, b), (a, 0)} :=
    (exists_unique_normal_corner
      ((hrim i).subset (show p i ∈ ({p i, q i} : Set (ℝ × ℝ)) by simp)).2
      ((hrim i).subset (show q i ∈ ({p i, q i} : Set (ℝ × ℝ)) by simp)).2
      (hpv i) (hqv i) (hleft i) (hbottom i) (hdiagonal i)).exists
  choose c a ha b hb htype using hex
  have hpoint (i : ι) : cornerMap (c i) (a i, 0) ∈ D i := by
    apply (hD i).1
    apply (mem_cornerMap_image (c i) {p i, q i} (a i, 0)).mp
    exact (htype i).symm.subset (by simp)
  have hinj (i j : ι) (hc : c i = c j) (he : a i = a j) : i = j := by
    by_contra hn
    exact disjoint_left.mp (hdis hn) (hpoint i) (by simpa only [hc, he] using hpoint j)
  have hcard := corner_order_cardinality c a hinj
  exact ⟨c, a, b, ha, hb, htype, hinj, hcard.1, hcard.2⟩

end PoincareConjecture.M76.TriangleCorner
