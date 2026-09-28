import PoincareConjecture.Proofs.M04.ShiJoinedDensity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "End" => E →L[ℝ] E
local notation "Data" => ℝ × ((E × (E × End)) × ((E × End) × (E × End)))

def shiJoinedAtlasTuples {κ : Type*}
    (c : κ → OpenPartialHomeomorph M E) (K : κ → Set M)
    (a b L R : ℝ) (k l r : κ) : Set Data :=
  shiJoinedCompactTuples a b L R ((c k) '' K k)
    ((c l) '' (K k ∩ K l)) ((c r) '' (K k ∩ K r))

theorem exists_shiJoinedAtlas_uniform_bound [T2Space M]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D : LeviCivitaData g)
    (c : κ → OpenPartialHomeomorph M E) (K : κ → Set M)
    (hc : ∀ k, ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ (c k) (c k).source)
    (hi : ∀ k, ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ (c k).symm (c k).target)
    (hK : ∀ k, IsCompact (K k)) (hKs : ∀ k, K k ⊆ (c k).source)
    (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (L R : ℝ) (hL : 1 ≤ L) (hR : 0 ≤ R) :
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ B ∧
      ∀ (i : ι) (k l r : κ),
        shiJoinedAtlasTuples c K (a i) (b i) L R k l r ×ˢ
            Metric.closedBall (0 : E) ρ ⊆
          shiJoinedDomain D (c k) (c l) (c r) (a i) (b i) ∧
        ∀ p ∈ shiJoinedAtlasTuples c K (a i) (b i) L R k l r,
          let f := shiJoinedDensity g D (c k) (c l) (c r) (a i) (b i) p
          ‖fderiv ℝ f 0‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ f) 0‖ ≤ B ∧
          (∀ v w, fderiv ℝ (fderiv ℝ f) 0 v w =
            fderiv ℝ (fderiv ℝ f) 0 w v) ∧
          ∀ z, ‖z‖ ≤ ρ →
            |f z - f 0 - fderiv ℝ f 0 z - fderiv ℝ (fderiv ℝ f) 0 z z / 2| ≤
              B * ‖z‖ ^ 3 := by
  classical
  have hcore (k l r : κ) := shiJoinedCore_coordinate_sets (c k) (c l) (c r)
    (hK k) (hK l) (hK r) (hKs k) (hKs l) (hKs r)
  have hlocal (j : ι × κ × κ × κ) :=
    exists_shiJoinedDensity_uniform_bound D
      (hc j.2.1) (hi j.2.1) (hc j.2.2.1) (hi j.2.2.1)
      (hc j.2.2.2) (hi j.2.2.2) (a j.1) (b j.1) L R (hab j.1) hL hR
      (hcore j.2.1 j.2.2.1 j.2.2.2).1
      (hcore j.2.1 j.2.2.1 j.2.2.2).2.1
      (hcore j.2.1 j.2.2.1 j.2.2.2).2.2.1
      (hcore j.2.1 j.2.2.1 j.2.2.2).2.2.2.1
      (hcore j.2.1 j.2.2.1 j.2.2.2).2.2.2.2.1
      (hcore j.2.1 j.2.2.1 j.2.2.2).2.2.2.2.2
  choose ρj Bj hρj hρj1 hBj hdomain hbound using hlocal
  let ρ : ℝ := ∏ j, ρj j
  let B : ℝ := 1 + ∑ j, Bj j
  have hρ : 0 < ρ := Finset.prod_pos (fun j _ => hρj j)
  have hρ1 : ρ ≤ 1 :=
    Finset.prod_le_one (fun j _ => (hρj j).le) (fun j _ => hρj1 j)
  have hρle (j : ι × κ × κ × κ) : ρ ≤ ρj j := by
    have hsubset : ({j} : Finset (ι × κ × κ × κ)) ⊆ Finset.univ :=
      Finset.subset_univ _
    simpa only [Finset.prod_singleton] using
      Finset.prod_le_prod_of_subset_of_le_one hsubset
        (fun k _ => (hρj k).le) (fun k _ _ => hρj1 k)
  have hsum : 0 ≤ ∑ j, Bj j :=
    Finset.sum_nonneg (fun j _ => zero_le_one.trans (hBj j))
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hsum]
  have hBle (j : ι × κ × κ × κ) : Bj j ≤ B := by
    have hsingle := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset (ι × κ × κ × κ))) =>
        zero_le_one.trans (hBj k)) (Finset.mem_univ j)
    dsimp only [B]
    linarith only [hsingle]
  refine ⟨ρ, B, hρ, hρ1, hB, ?_⟩
  intro i k l r
  let j : ι × κ × κ × κ := (i, k, l, r)
  constructor
  · intro q hq
    exact hdomain j ⟨hq.1, Metric.closedBall_subset_closedBall (hρle j) hq.2⟩
  · intro p hp
    obtain ⟨hfirst, hsecond, hsym, herror⟩ := hbound j p hp
    refine ⟨hfirst.trans (hBle j), hsecond.trans (hBle j), hsym, ?_⟩
    intro z hz
    exact (herror z (hz.trans (hρle j))).trans
      (mul_le_mul_of_nonneg_right (hBle j) (pow_nonneg (norm_nonneg z) 3))

end PoincareConjecture.M04
