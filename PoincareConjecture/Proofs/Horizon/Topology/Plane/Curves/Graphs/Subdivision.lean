


import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas










set_option autoImplicit false

open Set Metric
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves




theorem exists_finite_strictMono_projection_subdivision
    {f : ℝ → EuclideanSpace ℝ (Fin 2)} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) (hregular : ∀ t ∈ Icc a b, deriv f t ≠ 0) :
    ∃ (n : ℕ) (c : Fin (n + 1) → ℝ) (v : Fin n → EuclideanSpace ℝ (Fin 2)),
      0 < n ∧ StrictMono c ∧ c 0 = a ∧ c (Fin.last n) = b ∧
      ∀ i, v i ≠ 0 ∧ (∃ s ∈ Icc a b, v i = deriv f s) ∧
        (∀ t ∈ Icc (c i.castSucc) (c i.succ), 0 < inner ℝ (v i) (deriv f t)) ∧
        StrictMonoOn (fun t => inner ℝ (v i) (f t)) (Icc (c i.castSucc) (c i.succ)) := by
  have hderiv : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  let U (s : Icc a b) : Set ℝ := {t | 0 < inner ℝ (deriv f s) (deriv f t)}
  have hopen (s : Icc a b) : IsOpen (U s) :=
    isOpen_lt continuous_const (continuous_const.inner hderiv)
  have hcover : Icc a b ⊆ ⋃ s, U s := by
    intro t ht
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, real_inner_self_pos.mpr (hregular t ht)⟩
  obtain ⟨δ, hδ, hsub⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hopen hcover
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hnpos : (0 : ℝ) < n := (div_pos (sub_pos.mpr hab) hδ).trans hn
  have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  let d : ℝ := (b - a) / n
  have hdpos : 0 < d := div_pos (sub_pos.mpr hab) hnpos
  have hdδ : d < δ := by
    apply (div_lt_iff₀ hnpos).mpr
    have h := (div_lt_iff₀ hδ).mp hn
    nlinarith
  let c (i : Fin (n + 1)) : ℝ := a + (i : ℝ) * d
  have hcmono : StrictMono c := by
    intro i j hij
    have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    simpa only [c, add_comm] using add_lt_add_left (mul_lt_mul_of_pos_right hcast hdpos) a
  have hczero : c 0 = a := by simp [c]
  have hclast : c (Fin.last n) = b := by
    dsimp [c, d]
    field_simp
    ring
  have hcbounds (i : Fin (n + 1)) : c i ∈ Icc a b := by
    constructor
    · rw [← hczero]
      exact hcmono.monotone (Fin.zero_le i)
    · rw [← hclast]
      exact hcmono.monotone (Fin.le_last i)
  have hstep (i : Fin n) : c i.succ - c i.castSucc = d := by
    simp only [c, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  have hcell (i : Fin n) : ∃ s : Icc a b,
      Icc (c i.castSucc) (c i.succ) ⊆ U s := by
    obtain ⟨s, hs⟩ := hsub (c i.castSucc) (hcbounds i.castSucc)
    refine ⟨s, fun t ht => hs ?_⟩
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have htd : t - c i.castSucc ≤ d := by linarith [hstep i, ht.2]
    exact htd.trans_lt hdδ
  choose sample hsample using hcell
  let v (i : Fin n) := deriv f (sample i)
  refine ⟨n, c, v, by exact_mod_cast hnpos, hcmono, hczero, hclast, ?_⟩
  intro i
  have hpositive : ∀ t ∈ Icc (c i.castSucc) (c i.succ),
      0 < inner ℝ (v i) (deriv f t) := hsample i
  refine ⟨hregular _ (sample i).property, ⟨sample i, (sample i).property, rfl⟩,
    hpositive, ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (continuous_const.inner hf.continuous).continuousOn
  intro t ht
  have hscalar : deriv (fun s => inner ℝ (v i) (f s)) t =
      inner ℝ (v i) (deriv f t) := by
    simpa using ((hasDerivAt_const t (v i)).inner ℝ
      ((hf.differentiable (by simp)) t).hasDerivAt).deriv
  rw [hscalar]
  exact hpositive t (interior_subset ht)

end Poincare.Topology.Plane.Curves
