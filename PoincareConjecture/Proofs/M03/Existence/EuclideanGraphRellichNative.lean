import PoincareConjecture.Proofs.M03.Existence.EuclideanRellichNative










set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators

namespace PoincareConjecture.EuclideanGraphRellichNative

open EuclideanTranslationNative EuclideanMollificationNative EuclideanRellichNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

abbrev GraphAmbient (n : ℕ) := ScalarL2 n × (Fin n → ScalarL2 n)


def derivativeGraphSet (K : Set E) : Set (GraphAmbient n) :=
  {u | ∃ f : E → ℝ, ∃ hf : ContDiff ℝ 1 f, ∃ hfL2 : MemLp f 2 volume,
    ∃ hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume,
      (∀ x ∉ K, f x = 0) ∧ u.1 = hfL2.toLp f ∧
        ∀ i, u.2 i = (hcoord i).toLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))}

theorem gradientEnergy_eq_sum_norm_sq {f : E → ℝ}
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume) :
    gradientEnergy f =
      ∑ i, ‖(hcoord i).toLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))‖ ^ 2 := by
  unfold gradientEnergy
  apply Finset.sum_congr rfl
  intro i _
  exact (scalar_toLp_norm_sq (hcoord i)).symm

theorem gradientEnergy_le_of_graph_norm {u : GraphAmbient n}
    {f : E → ℝ}
    (hcoord : ∀ i : Fin n,
      MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2 volume)
    (hu : ∀ i, u.2 i = (hcoord i).toLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)))
    {R : ℝ} (hR : 0 ≤ R) (huR : ‖u‖ ≤ R) :
    gradientEnergy f ≤ (((n : ℝ) + 1) * R) ^ 2 := by
  rw [gradientEnergy_eq_sum_norm_sq hcoord]
  calc
    _ = ∑ i : Fin n, ‖u.2 i‖ ^ 2 := by simp only [hu]
    _ ≤ ∑ _i : Fin n, R ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_sq₀ (norm_nonneg _) hR).mpr
        (((norm_le_pi_norm u.2 i).trans (norm_snd_le u)).trans huR)
    _ = (n : ℝ) * R ^ 2 := by simp
    _ ≤ ((n : ℝ) + 1) ^ 2 * R ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg R)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [sq_nonneg (n : ℝ)]
    _ = _ := (mul_pow ((n : ℝ) + 1) R 2).symm


theorem totallyBounded_rawGraph_value {K : Set E} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) :
    TotallyBounded (Prod.fst '' (derivativeGraphSet K ∩ Metric.ball 0 R)) := by
  apply totallyBounded_supported_C1 hK (D := ((n : ℝ) + 1) * R)
    (mul_nonneg (by positivity) hR) (R := R)
  · rintro _ ⟨u, ⟨_, huR⟩, rfl⟩
    exact (norm_fst_le u).trans
      (show ‖u‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using huR).le
  · rintro _ ⟨u, ⟨hu, huR⟩, rfl⟩
    obtain ⟨f, hf, hfL2, hcoord, hsupp, hvalue, hderiv⟩ := hu
    refine ⟨f, hf, hfL2, hcoord, hsupp, hvalue, ?_⟩
    apply gradientEnergy_le_of_graph_norm hcoord hderiv hR
    exact (show ‖u‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using huR).le


theorem totallyBounded_completedGraph_value {K : Set E} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) :
    TotallyBounded (Prod.fst '' (closure (derivativeGraphSet K) ∩ Metric.closedBall 0 R)) :=
  totallyBounded_bounded_graph_closure Prod.fst continuous_fst
    (totallyBounded_rawGraph_value hK (by linarith : 0 ≤ R + 1))


theorem isCompact_closure_completedGraph_value {K : Set E} (hK : IsCompact K)
    {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (closure
      (Prod.fst '' (closure (derivativeGraphSet K) ∩ Metric.closedBall 0 R))) :=
  (totallyBounded_completedGraph_value hK hR).closure.isCompact_of_isClosed isClosed_closure

end PoincareConjecture.EuclideanGraphRellichNative
