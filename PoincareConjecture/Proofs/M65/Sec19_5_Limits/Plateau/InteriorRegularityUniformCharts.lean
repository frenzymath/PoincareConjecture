import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityBoundedChart
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas











set_option autoImplicit false

open Set Metric
open scoped Topology ContDiff Manifold BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}





theorem m65Embedding_uniform_cone_charts (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M)) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧ ∀ q0 : M,
      ∃ (p : M) (L : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (P : EuclideanSpace ℝ (Fin 3) → M) (ρ : ℝ),
        0 < ρ ∧ P 0 = p ∧ ‖L‖ ≤ B ∧
        ContMDiffOn (𝓡 3) (𝓡 3) 1 P (ball 0 (2 * ρ)) ∧
        (∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ,
          ‖fderiv ℝ (e ∘ P) y‖ ≤ B) ∧
        ∀ q : M, dist (e q) (e q0) < δ →
          ‖L (e q - e p)‖ < ρ / 4 ∧ P (L (e q - e p)) = q := by
  classical
  choose L P ρ d K hρ hd hK hP0 hP hDbound hcapture using
    fun p => m65Embedding_exists_bounded_chart e he hinj hemb p
  have hS : IsCompact (range e) := by
    simpa only [image_univ] using compact.image he.continuous
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun p => ball (e p) (d p / 2)) (fun _ => isOpen_ball) (by
      rintro z ⟨p, rfl⟩
      exact mem_iUnion.mpr ⟨p, by simpa using div_pos (hd p) (by norm_num : (0 : ℝ) < 2)⟩)
  have hcover : range e ⊆ ⋃ p : ↥t, ball (e p) (d p / 2) := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := mem_iUnion₂.mp (ht hz)
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hz⟩
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric hS
    (fun p : ↥t => isOpen_ball (x := e p) (ε := d p / 2)) hcover
  let B := 1 + ∑ p ∈ t, (‖L p‖ + K p)
  have hterm (p : M) : 0 ≤ ‖L p‖ + K p := add_nonneg (norm_nonneg _) (hK p).le
  have hB : 0 < B := by
    dsimp only [B]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun p _ => hterm p)
  have hbounds (p : M) (hp : p ∈ t) : ‖L p‖ ≤ B ∧ K p ≤ B := by
    have hsum := Finset.single_le_sum (fun q _ => hterm q) hp
    dsimp only [B]
    constructor <;> linarith [norm_nonneg (L p), hK p]
  refine ⟨δ, B, hδ, hB, fun q0 => ?_⟩
  obtain ⟨p, hball⟩ := hballs (e q0) (mem_range_self q0)
  refine ⟨p, L p, P p, ρ p, hρ p, hP0 p, (hbounds p p.2).1, hP p, ?_, ?_⟩
  · intro y hy
    exact (hDbound p y hy).trans (hbounds p p.2).2
  · intro q hq
    apply hcapture p q
    exact (hball hq).trans (by linarith [hd p])

end PoincareConjecture
