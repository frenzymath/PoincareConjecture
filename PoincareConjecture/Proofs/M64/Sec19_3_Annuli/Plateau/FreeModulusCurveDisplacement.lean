import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ContDiff.Operations















set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M64





theorem exists_small_c1_periodic_translation_disjoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {P eps : ℝ} (heps : 0 < eps)
    {c0 c1 : ℝ → E}
    (hc0 : ContDiff ℝ 1 c0) (hc1 : ContDiff ℝ 1 c1)
    (_hp0 : Function.Periodic c0 P) (hp1 : Function.Periodic c1 P)
    (hdim : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ E) :
    ∃ v : E, ‖v‖ < eps ∧
      Function.Periodic (fun x => c1 x + v) P ∧
      ContDiff ℝ 1 (fun x => c1 x + v) ∧
      Disjoint (range c0) (range (fun x => c1 x + v)) := by
  let d : ℝ × ℝ → E := fun p => c0 p.1 - c1 p.2
  have hd : ContDiff ℝ 1 d := by
    have h0 : ContDiff ℝ 1 (fun p : ℝ × ℝ => c0 p.1) :=
      contDiffOn_univ.1 ((contDiffOn_univ.2 hc0).comp
        (contDiffOn_univ.2 contDiff_fst) (subset_univ _))
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => c1 p.2) :=
      contDiffOn_univ.1 ((contDiffOn_univ.2 hc1).comp
        (contDiffOn_univ.2 contDiff_snd) (subset_univ _))
    exact ContDiff.sub h0 h1
  have hdense : Dense (range d)ᶜ :=
    ContDiff.dense_compl_range_of_finrank_lt_finrank hd hdim
  obtain ⟨v, hv, hvdist⟩ := hdense.exists_dist_lt (0 : E) heps
  have hvnorm : ‖v‖ < eps := by
    convert hvdist using 1
    simp [dist_eq_norm]
  have hperiod : Function.Periodic (fun x => c1 x + v) P := by
    intro x
    change c1 (x + P) + v = c1 x + v
    rw [hp1 x]
  have hregular : ContDiff ℝ 1 (fun x => c1 x + v) := by
    exact contDiffOn_univ.1 ((contDiffOn_univ.2 hc1).add
      (contDiffOn_univ.2 contDiff_const))
  refine ⟨v, hvnorm, hperiod, hregular, ?_⟩
  rw [disjoint_left]
  intro z hz0 hz1
  rcases hz0 with ⟨x, hx⟩
  rcases hz1 with ⟨y, hy⟩
  apply hv
  refine ⟨(x, y), ?_⟩
  change c0 x - c1 y = v
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using hx.trans hy.symm




theorem exists_small_euclidean_periodic_translation_disjoint
    {n : ℕ} (hn : 3 ≤ n) {P eps : ℝ} (heps : 0 < eps)
    {c0 c1 : ℝ → EuclideanSpace ℝ (Fin n)}
    (hc0 : ContDiff ℝ 1 c0) (hc1 : ContDiff ℝ 1 c1)
    (hp0 : Function.Periodic c0 P) (hp1 : Function.Periodic c1 P) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ < eps ∧
      Function.Periodic (fun x => c1 x + v) P ∧
      ContDiff ℝ 1 (fun x => c1 x + v) ∧
      Disjoint (range c0) (range (fun x => c1 x + v)) := by
  apply exists_small_c1_periodic_translation_disjoint heps hc0 hc1 hp0 hp1
  simpa [EuclideanSpace] using (show 2 < n by omega)





theorem exists_translation_radius_subset_open
    {E : Type*} [NormedAddCommGroup E] {U : Set E} (hU : IsOpen U)
    {P eps : ℝ} (hP : 0 < P)
    {c : ℝ → E} (hc : Continuous c) (hp : Function.Periodic c P)
    (hcU : ∀ x ∈ Icc (0 : ℝ) P, c x ∈ U) (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ eps ∧
      ∀ v : E, ‖v‖ < δ → ∀ x : ℝ, c x + v ∈ U := by
  let K : Set E := c '' Icc (0 : ℝ) P
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hc.continuousOn
  have hKU : K ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact hcU x hx
  obtain ⟨δ₀, hδ₀, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  let δ := min eps δ₀
  have hδ : 0 < δ := lt_min heps hδ₀
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro v hv x
  obtain ⟨x', hx', hxx⟩ := hp.exists_mem_Ico₀ hP x
  have hxI : x' ∈ Icc (0 : ℝ) P := ⟨hx'.1, hx'.2.le⟩
  have hmem : c x' ∈ K := ⟨x', hxI, rfl⟩
  have hsmall : ‖v‖ < δ₀ := lt_of_lt_of_le hv (min_le_right _ _)
  have hth : c x' + v ∈ Metric.thickening δ₀ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨c x', hmem, ?_⟩
    simpa [dist_add_left] using hsmall
  rw [hxx]
  exact hthick hth

end PoincareConjecture.M64
