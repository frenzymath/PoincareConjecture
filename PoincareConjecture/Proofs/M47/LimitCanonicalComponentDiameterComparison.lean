import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalCoefficientJets
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentImage
import PoincareConjecture.Proofs.M47.SeedLimitPhysicalTangent
import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitCanonical_component_eventually_diameter_comparison
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    {L : ℝ} (hL : 1 < L) :
    ∀ᶠ k in atTop,
      let f := limitCanonicalPhysicalTerminalChart G F R k
      let g := M13.scaleSmoothMetric
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      G.exhaustion.space k = univ ∧
        f.target = connectedComponent (f G.limit.base) ∧
        intrinsicDiameter g f.target ≤
          ENNReal.ofReal L * intrinsicDiameter (G.limit.flow.metric 0) univ ∧
        intrinsicDiameter (G.limit.flow.metric 0) univ ≤
          ENNReal.ofReal L * intrinsicDiameter g f.target := by
  have hLpos : 0 < L := zero_lt_one.trans hL
  have hinv : L⁻¹ < 1 := (inv_lt_one₀ hLpos).mpr hL
  filter_upwards [Proofs.M47.seedLimit_eventually_physical_tangent_comparison G F R
    hcompact 0 G.limit.zero_mem (inv_pos.mpr hLpos) hinv,
    limitCanonical_eventually_physical_component_image G F R hcompact] with k hk hfull
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let g0 := G.limit.flow.metric 0
  let g : RiemannianMetric 3
      ((F (G.subsequence k)).slice
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).carrier :=
    M13.scaleSmoothMetric ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
      (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have ht := limitCanonical_terminal_clock_mem G k
  have hsource : f.source = univ :=
    (limitCanonicalPhysicalChart_source _ _ _ _ _ _).trans hfull.1
  have hroot : 0 < Real.sqrt (V.scale (G.subsequence k)) :=
    Real.sqrt_pos.mpr (V.base_scalar_pos (G.subsequence k))
  have hnorm (x : G.limit.sliceCarrier.carrier) (v : TangentSpace (𝓡 3) x) :
      g0.tangentNorm x v ≤ L * g.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ∧
      g.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ L * g0.tangentNorm x v := by
    have hn := hk.2.2 h0 ht x (mem_univ x) v
    change g0.tangentNorm x v ≤ (Real.sqrt (V.scale (G.subsequence k)) / L⁻¹) *
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).tangentNorm
          (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ∧
      ((F (G.subsequence k)).metric
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).tangentNorm
        (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
          (1 / (L⁻¹ * Real.sqrt (V.scale (G.subsequence k)))) * g0.tangentNorm x v at hn
    constructor
    · refine hn.1.trans_eq ?_
      change _ = L * RiemannianMetric.tangentNorm (M13.scaleSmoothMetric _ _ _) _ _
      rw [M13.scaleSmoothMetric_tangentNorm, div_inv_eq_mul]
      ring
    · change RiemannianMetric.tangentNorm (M13.scaleSmoothMetric _ _ _) _ _ ≤ _
      rw [M13.scaleSmoothMetric_tangentNorm]
      apply (mul_le_mul_of_nonneg_left hn.2 hroot.le).trans_eq
      field_simp
  have hforward : intrinsicDiameter g f.target ≤
      ENNReal.ofReal L * intrinsicDiameter g0 univ := by
    have h := g0.intrinsicDiameter_image_le_mul_of_isOpen g f isOpen_univ
      (hsource ▸ f.contMDiffOn_toFun.of_le (by simp)) hLpos
      (fun x _ v => (hnorm x v).2)
    have himage : f '' univ = f.target := by
      simpa only [hsource] using f.toPartialEquiv.image_source_eq_target
    rwa [himage] at h
  have hinverse : intrinsicDiameter g0 univ ≤
      ENNReal.ofReal L * intrinsicDiameter g f.target := by
    have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 f f.source :=
      f.contMDiffOn_toFun.of_le (by simp)
    have hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 f.symm f.target :=
      f.contMDiffOn_invFun.of_le (by simp)
    have h := g.intrinsicDiameter_image_le_mul_of_isOpen g0 f.symm f.open_target hi hLpos
      (fun y hy v => g0.inverse_tangentNorm_le_of_forward_lower_bound g
        f.toOpenPartialHomeomorph hf hi hy (fun w => (hnorm (f.symm y) w).1) v)
    have himage : f.symm '' f.target = univ := by
      exact f.toPartialEquiv.symm.image_source_eq_target.trans hsource
    rwa [himage] at h
  exact ⟨hfull.1, hfull.2 0 h0 ht, hforward, hinverse⟩

end PoincareConjecture.M47
