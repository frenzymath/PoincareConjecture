import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapRadial
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapSides
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallBoundaryParametrization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarOrientation

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_native_cap_chart
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (tag : SurgeryCapTag ψ u)
    (A : BallNeighborhoodChart E3 E3)
    (hboundary : A.boundary = ψ '' (univ ×ˢ ({0} : Set ℝ)))
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (hnormalized : A.chart ''
      {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} = tag.cap)
    (b0 : ℝ) (hb0 : 0 < b0) :
    ∃ g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      (∀ q : UnitTwoSphere, A.chart (g q : E3) = ψ (q, 0)) ∧
      ∃ e : ℝ, ∃ he : e * e = 1, ∃ ε b : ℝ,
        0 < ε ∧ 0 < b ∧ b < b0 ∧
        let Q := nativeCapSourceChart ψ u tag a ha g
        let C := nativeCapRadialChart ψ u tag Q e he
        ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ Q Q.source ∧
        ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ Q.symm Q.target ∧
        closedBall (0 : E2) (1 + ε) ⊆ Q.source ∧
        Q '' closedBall (0 : E2) 1 =
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
        (∀ X : E2, ‖X‖ ≤ 1 + ε →
          (heightCoordinates (Q X : E3)).2 < tag.overlapWidth) ∧
        ContDiffOn ℝ ∞ C C.source ∧
        ContDiffOn ℝ ∞ C.symm C.target ∧
        closedBall (0 : E2) (1 + ε) ×ˢ Icc (-b) b ⊆ C.source ∧
        (∀ X : E2, ‖X‖ ≤ 1 + ε →
          C (X, 0) = A.chart (referenceCapPoint a X)) ∧
        (∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ, |s| ≤ b →
          (C (X, s) ∈ A.boundary ↔ s = 0)) ∧
        (∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ,
          -b < s → s < 0 → C (X, s) ∈ A.inside) ∧
        ∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ,
          0 < s → s < b → C (X, s) ∈ A.closedRegionᶜ := by
  obtain ⟨g, hg⟩ := exists_ball_boundary_parametrization ψ hψ A hboundary
  let Q := nativeCapSourceChart ψ u tag a ha g
  obtain ⟨_, _, _, _, hQ, hQi, _, himage, R, hR, hRsource, hRband, hRcentral⟩ :=
    nativeCapSourceChart_spec ψ u tag A a ha g hg hnormalized
  let qS := southSpherePoint (0 : E2)
  have hqS : heightCoordinates (qS : E3) = (0, -1) := by
    simpa only [qS, norm_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
      Real.sqrt_one] using southSpherePoint_coordinates (0 : E2) (by norm_num)
  have hqSimage : qS ∈ Q '' closedBall (0 : E2) 1 := by
    rw [himage]
    change (heightCoordinates (qS : E3)).2 ≤ 0
    rw [hqS]
    norm_num
  obtain ⟨X0, hX0, hQX0⟩ := hqSimage
  have hflat : tag.flatChart (0 : E2) = tag.sourceChart qS := by
    have hh := tag.flat_eq qS (by rw [hqS]; norm_num) (by rw [hqS]; norm_num)
    simpa only [hqS] using hh
  obtain ⟨θ, hθ, hθneg, hθpos⟩ := exists_ball_collar_orientation ψ hψ A hboundary
  have hθne : θ ≠ 0 := by intro hz; rw [hz, zero_mul] at hθ; exact zero_ne_one hθ
  have hsign : tag.sign ≠ 0 := by
    intro hz
    have hh := tag.sign_abs
    rw [hz, abs_zero] at hh
    exact zero_ne_one hh
  let k : ℝ := -(tag.sign * tag.scale) / tag.beta
  have hk : k ≠ 0 := div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hsign tag.scale_pos.ne'))
    tag.beta_ne
  have hθk : θ * k ≠ 0 := mul_ne_zero hθne hk
  obtain ⟨e, he, hτ⟩ : ∃ e : ℝ, e * e = 1 ∧ 0 < θ * k * e := by
    rcases lt_or_gt_of_ne hθk with hn | hp
    · refine ⟨-1, by norm_num, ?_⟩
      nlinarith only [hn]
    · exact ⟨1, by norm_num, by simpa only [mul_one] using hp⟩
  let τ : ℝ := θ * k * e
  have heabs : |e| = 1 := by nlinarith only [sq_abs e, abs_nonneg e, he]
  have hke : k * e = θ * τ := by
    calc
      k * e = (θ * θ) * (k * e) := by rw [hθ, one_mul]
      _ = θ * τ := by dsimp only [τ]; ring
  let C := nativeCapRadialChart ψ u tag Q e he
  obtain ⟨_, _, hCf, _, hC, hCi, hCzero⟩ := nativeCapRadialChart_spec ψ u tag Q hQ hQi e he
  obtain ⟨_, _, _, hDpole⟩ := nativeCapAmbientDiffeomorph_spec ψ u tag
  have hcentral (X : E2) (hX : ‖X‖ < R) :
      C (X, 0) = A.chart (referenceCapPoint a X) :=
    (hCzero X (hRsource (mem_closedBall_zero_iff.mpr hX.le))).2.trans (hRcentral X hX.le)
  have hzero (X : E2) (hX : ‖X‖ < R) : (X, (0 : ℝ)) ∈ C.source :=
    (hCzero X (hRsource (mem_closedBall_zero_iff.mpr hX.le))).1
  let d : ℝ := min (tag.collarWidth / (|k| + 1)) (1 / (τ + 1)) / 2
  have hk1 : 0 < |k| + 1 := by positivity
  have hτ1 : 0 < τ + 1 := by dsimp only [τ]; linarith only [hτ]
  have hm : 0 < min (tag.collarWidth / (|k| + 1)) (1 / (τ + 1)) :=
    lt_min (div_pos tag.collar_pos hk1) (div_pos zero_lt_one hτ1)
  have hd : 0 < d := div_pos hm (by norm_num)
  have hd1 : d < tag.collarWidth / (|k| + 1) := by
    dsimp only [d]
    linarith only [hm, min_le_left (tag.collarWidth / (|k| + 1)) (1 / (τ + 1))]
  have hd2 : d < 1 / (τ + 1) := by
    dsimp only [d]
    linarith only [hm, min_le_right (tag.collarWidth / (|k| + 1)) (1 / (τ + 1))]
  have htime (s : ℝ) (hs : |s| < d) :
      |k * e * s| < tag.collarWidth ∧ |τ * s| < 1 := by
    have hh1 := (lt_div_iff₀ hk1).mp (hs.trans hd1)
    have hh2 := (lt_div_iff₀ hτ1).mp (hs.trans hd2)
    constructor
    · rw [abs_mul, abs_mul, heabs, mul_one]
      nlinarith only [hh1, abs_nonneg s]
    · rw [abs_mul, abs_of_pos hτ]
      nlinarith only [hh2, abs_nonneg s]
  have hanchor (s : ℝ) (hs : |s| < d) :
      C (X0, s) = ψ (tag.sourceChart qS, θ * (τ * s)) := by
    rw [hCf, hQX0, hDpole]
    have hcollar := tag.collar_eq (0 : E2) (by norm_num) (k * e * s) (htime s hs).1
    rw [hflat] at hcollar
    have hheight : tag.cutHeight + tag.sign * (tag.removal - tag.scale * (1 + e * s)) =
        tag.cutHeight + tag.sign * (tag.removal - tag.scale) + tag.beta * (k * e * s) := by
      dsimp only [k]
      field_simp [tag.beta_ne]
      ring
    rw [hheight, ← hcollar, hke, mul_assoc]
  have hanchor_neg (s : ℝ) (hs : -d < s) (hs0 : s < 0) : C (X0, s) ∈ A.inside := by
    have hsabs : |s| < d := abs_lt.mpr ⟨hs, hs0.trans hd⟩
    rw [hanchor s hsabs]
    exact hθneg ⟨(tag.sourceChart qS, τ * s),
      ⟨mem_univ _, (abs_lt.mp (htime s hsabs).2).1, mul_neg_of_pos_of_neg hτ hs0⟩, rfl⟩
  have hanchor_pos (s : ℝ) (hs0 : 0 < s) (hs : s < d) : C (X0, s) ∈ A.closedRegionᶜ := by
    have hsabs : |s| < d := abs_lt.mpr ⟨(neg_lt_zero.mpr hd).trans hs0, hs⟩
    rw [hanchor s hsabs]
    exact hθpos ⟨(tag.sourceChart qS, τ * s),
      ⟨mem_univ _, mul_pos hτ hs0, (abs_lt.mp (htime s hsabs).2).2⟩, rfl⟩
  obtain ⟨ε, b, hε, hεR, hb, hbb0, _, hcylinder, hboundaryC, hneg, hpos⟩ :=
    exists_cap_chart_side_buffer A C a ha R hR hzero hcentral X0
      (mem_closedBall_zero_iff.mp hX0) d b0 hd hb0 hanchor_neg hanchor_pos
  refine ⟨g, hg, e, he, ε, b, hε, hb, hbb0, hQ, hQi, ?_, himage, ?_,
    hC, hCi, hcylinder, ?_, hboundaryC, hneg, hpos⟩
  · intro X hX
    exact hRsource (mem_closedBall_zero_iff.mpr ((mem_closedBall_zero_iff.mp hX).trans hεR.le))
  · intro X hX
    exact hRband X (hX.trans hεR.le)
  · intro X hX
    exact hcentral X (hX.trans_lt hεR)

end PoincareConjecture.M25.Topology3D
