import PoincareConjecture.Proofs.M36.ComparisonCovariantJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance capLocalCoefficientNorm : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance capLocalCoefficientSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace



theorem exists_cap_coefficient_family_germ {J : Set ℝ} {U : Set E}
    (hU : IsOpen U) (A : ℝ × E → Bilin)
    (hA : ∀ t, ContDiffOn ℝ ∞ (fun y => A (t, y)) U)
    (hJoint : ContDiffOn ℝ ∞ A (J ×ˢ U)) {x : E} (hx : x ∈ U) :
    ∃ B : ℝ × E → Bilin, (∀ t, ContDiff ℝ ∞ (fun y => B (t, y))) ∧
      ContDiffOn ℝ ∞ B (J ×ˢ univ) ∧
      ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
        ∀ t : ℝ, ∀ y ∈ V, B (t, y) = A (t, y) := by
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let bump : ContDiffBump x :=
    { rIn := d / 4
      rOut := d / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith only [hd] }
  have hsupp : tsupport bump ⊆ U := by
    rw [bump.tsupport_eq]
    intro y hy
    apply hball
    have hdist : dist y x ≤ d / 2 := hy
    exact hdist.trans_lt (half_lt_self hd)
  let B : ℝ × E → Bilin := fun p => bump p.2 • A p
  have hB (t : ℝ) : ContDiff ℝ ∞ (fun y => B (t, y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport bump
    · exact bump.contDiff.contDiffAt.smul ((hA t).contDiffAt (hU.mem_nhds (hsupp hy)))
    · apply (contDiffAt_const (c := (0 : Bilin))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [B, hz]
  have hBJ : ContDiffOn ℝ ∞ B (J ×ˢ univ) := by
    rintro ⟨t, y⟩ ⟨ht, _⟩
    by_cases hy : y ∈ tsupport bump
    · have hlocal : ContDiffWithinAt ℝ ∞ B (J ×ˢ U) (t, y) :=
        (bump.contDiff.comp contDiff_snd).contDiffWithinAt.smul (hJoint _ ⟨ht, hsupp hy⟩)
      apply hlocal.mono_of_mem_nhdsWithin
      exact nhdsWithin_prod self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds (hsupp hy)))
    · have hzero : ContDiffWithinAt ℝ ∞ (fun _ : ℝ × E => (0 : Bilin))
          (J ×ˢ univ) (t, y) := contDiffWithinAt_const
      apply hzero.congr_of_eventuallyEq_of_mem (hx := ⟨ht, mem_univ y⟩)
      have heq0 : ∀ᶠ z in 𝓝 y, bump z = 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
        simpa only [Pi.zero_apply] using hz
      have hsnd : Tendsto (Prod.snd : ℝ × E → E) (𝓝 (t, y)) (𝓝 y) :=
        continuous_snd.tendsto (t, y)
      have heq : ∀ᶠ p : ℝ × E in 𝓝 (t, y), bump p.2 = 0 :=
        hsnd.eventually heq0
      filter_upwards [mem_nhdsWithin_of_mem_nhds heq] with p hp
      simp [B, hp]
  refine ⟨B, hB, hBJ, Metric.ball x (d / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_, ?_⟩
  · intro y hy
    apply hball
    exact (show dist y x < d / 4 from hy).trans (by linarith only [hd])
  · intro t y hy
    have hby : bump y = 1 := bump.one_of_mem_closedBall (Metric.mem_closedBall.mpr hy.le)
    simp only [B, hby, one_smul]

end PoincareConjecture.M47
