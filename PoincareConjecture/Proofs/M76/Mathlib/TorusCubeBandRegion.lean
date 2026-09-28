import PoincareConjecture.Proofs.M76.Mathlib.CenteredTorusCubeChart










set_option autoImplicit false

open Set Geometry

namespace TorusCube




def crossingBands (p d : ℝ) : Set ((AddCircle p × AddCircle p) × AddCircle p) :=
  {z | z.1.1 ∈ ((↑) : ℝ → AddCircle p) '' Ioo (-d) d ∨
    z.1.2 ∈ ((↑) : ℝ → AddCircle p) '' Ioo (-d) d ∨
    z.2 ∈ ((↑) : ℝ → AddCircle p) '' Ioo (-d) d}

variable (p : ℝ) [Fact (0 < p)]



theorem centeredCubeQuotient_mem_crossingBands_iff {d : ℝ}
    (hd : 0 < d) (hdhalf : d < p / 2) {x : CubeShell.Ambient}
    (hx : ‖x‖ < p / 2) :
    AddCircle.centeredCubeQuotient p x ∈ crossingBands p d ↔ p / 2 - d < ‖x‖ := by
  have hcoords : (|x.1.1| < p / 2 ∧ |x.1.2| < p / 2) ∧ |x.2| < p / 2 := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using hx
  have hinterval {s : ℝ} (hs : |s| < p / 2) : s ∈ Ioo (-p / 2) (p / 2) := by
    have h := abs_lt.mp hs
    constructor <;> linarith [h.1, h.2]
  rw [AddCircle.centeredCubeQuotient_apply]
  change ((((p / 2 + x.1.1 : ℝ) : AddCircle p) ∈
      ((↑) : ℝ → AddCircle p) '' Ioo (-d) d) ∨
    (((p / 2 + x.1.2 : ℝ) : AddCircle p) ∈
      ((↑) : ℝ → AddCircle p) '' Ioo (-d) d) ∨
    (((p / 2 + x.2 : ℝ) : AddCircle p) ∈
      ((↑) : ℝ → AddCircle p) '' Ioo (-d) d)) ↔ _
  rw [AddCircle.coe_center_mem_shortArc_iff p hd hdhalf (hinterval hcoords.1.1),
    AddCircle.coe_center_mem_shortArc_iff p hd hdhalf (hinterval hcoords.1.2),
    AddCircle.coe_center_mem_shortArc_iff p hd hdhalf (hinterval hcoords.2)]
  simp only [Prod.norm_def, Real.norm_eq_abs, lt_max_iff, or_assoc]



theorem outside_centeredCubeQuotient_mem_crossingBands {d : ℝ} (hd : 0 < d)
    (z : (AddCircle p × AddCircle p) × AddCircle p)
    (hz : z ∉ (AddCircle.centeredCubeQuotient p).target) : z ∈ crossingBands p d := by
  rw [AddCircle.centeredCubeQuotient_target] at hz
  have hzero : (0 : AddCircle p) ∈ ((↑) : ℝ → AddCircle p) '' Ioo (-d) d :=
    ⟨0, ⟨by linarith, hd⟩, by simp⟩
  by_cases h1 : z.1.1 = 0
  · exact Or.inl (h1.symm ▸ hzero)
  by_cases h2 : z.1.2 = 0
  · exact Or.inr (Or.inl (h2.symm ▸ hzero))
  have h3 : z.2 = 0 := by
    by_contra hn
    exact hz ⟨⟨h1, h2⟩, hn⟩
  exact Or.inr (Or.inr (h3.symm ▸ hzero))



theorem closedCube_subset_source {R : ℝ} (hR : R < p / 2) :
    {x : CubeShell.Ambient | ‖x‖ ≤ R} ⊆ (AddCircle.centeredCubeQuotient p).source := by
  intro x hx
  rw [AddCircle.centeredCubeQuotient_source]
  exact hx.trans_lt hR



theorem isCompact_centeredCubeImage {R : ℝ} (hR : R < p / 2) :
    IsCompact (AddCircle.centeredCubeQuotient p '' {x : CubeShell.Ambient | ‖x‖ ≤ R}) := by
  have hK : IsCompact {x : CubeShell.Ambient | ‖x‖ ≤ R} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      isCompact_closedBall (0 : CubeShell.Ambient) R
  exact hK.image_of_continuousOn ((AddCircle.centeredCubeQuotient p).continuousOn_toFun.mono
    (closedCube_subset_source p hR))




theorem crossingBands_subset_compl_centeredCubeImage {d R : ℝ}
    (hd : 0 < d) (hdhalf : d < p / 2) (hR : R ≤ p / 2 - d) :
    crossingBands p d ⊆
      (AddCircle.centeredCubeQuotient p '' {x : CubeShell.Ambient | ‖x‖ ≤ R})ᶜ := by
  intro z hz
  rintro ⟨x, hx, rfl⟩
  have hxB : ‖x‖ < p / 2 := lt_of_le_of_lt hx (by linarith)
  have hxband := (centeredCubeQuotient_mem_crossingBands_iff p hd hdhalf hxB).mp hz
  exact (not_lt_of_ge (hx.trans hR)) hxband




theorem compl_centeredCubeImage_subset_crossingBands {d R : ℝ}
    (hd : 0 < d) (hdhalf : d < p / 2) (hR : p / 2 - d ≤ R) :
    (AddCircle.centeredCubeQuotient p '' {x : CubeShell.Ambient | ‖x‖ ≤ R})ᶜ ⊆
      crossingBands p d := by
  let Q := AddCircle.centeredCubeQuotient p
  intro z hz
  by_cases hzQ : z ∈ Q.target
  · have hxQ : Q.symm z ∈ Q.source := Q.map_target hzQ
    have hxB : ‖Q.symm z‖ < p / 2 := by
      simpa only [Q, AddCircle.centeredCubeQuotient_source, mem_ofPred_eq] using hxQ
    have hxR : R < ‖Q.symm z‖ := by
      by_contra h
      exact hz ⟨Q.symm z, le_of_not_gt h, Q.right_inv hzQ⟩
    have hband := (centeredCubeQuotient_mem_crossingBands_iff p hd hdhalf hxB).mpr
      (hR.trans_lt hxR)
    change Q (Q.symm z) ∈ crossingBands p d at hband
    simpa only [Q.right_inv hzQ] using hband
  · exact outside_centeredCubeQuotient_mem_crossingBands p hd z hzQ

end TorusCube
