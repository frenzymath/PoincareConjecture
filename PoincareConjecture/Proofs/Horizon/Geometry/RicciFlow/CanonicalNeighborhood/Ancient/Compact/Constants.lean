import PoincareConjecture.Statements.M26CanonicalNeighborhoods

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {t epsilon C C' : ℝ}

def StrongCapCertificate.mono_constant
    (N : StrongCapCertificate K t epsilon C) (hC : C ≤ C') :
    StrongCapCertificate K t epsilon C' := by
  refine {
    N with
    constant_pos := N.constant_pos.trans_le hC
    cap_constant := N.cap_constant.trans hC
    intrinsic_diameter_scale := N.intrinsic_diameter_scale.trans_le ?_
    scalar_ratio := fun x hx y hy => (N.scalar_ratio x hx y hy).trans
      (mul_le_mul_of_nonneg_right hC (N.scalar_pos x hx).le)
    volume_bound := N.volume_bound.trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hC) le_rfl)
    gradient_bound := fun x hx => (N.gradient_bound x hx).trans
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (N.scalar_pos x hx).le _))
    laplacian_bound := fun x hx => (N.laplacian_bound x hx).trans
      (mul_le_mul_of_nonneg_right hC (sq_nonneg _))
    core_ball_scale := ?_
  }
  · have hpos := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le N.intrinsic_diameter_scale)
    have hscale : 0 ≤ scalarCurvatureSupOn (K.flow.metric t) (K.flow.connection t)
        N.cap.carrier ^ (-1 / 2 : ℝ) :=
      (pos_of_mul_pos_right hpos N.constant_pos.le).le
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC hscale)
  · intro y hy
    obtain ⟨r, hr, hscale, hball, hcompact, hvolume⟩ := N.core_ball_scale y hy
    exact ⟨r, hr, hscale, hball, hcompact,
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (inv_anti₀ N.constant_pos hC) (pow_nonneg hr.le 3))).trans hvolume⟩

def M26StrongDoubleCappedTube.mono_constant
    (N : M26StrongDoubleCappedTube K t epsilon C) (hC : C ≤ C') :
    M26StrongDoubleCappedTube K t epsilon C' := {
  N with
  constant_pos := N.constant_pos.trans_le hC
  cap₁ := N.cap₁.mono_constant hC
  cap₂ := N.cap₂.mono_constant hC
}

theorem CompactSmallSliceCertificate.mono_constant
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (N : CompactSmallSliceCertificate K C) (hC : C ≤ C') :
    CompactSmallSliceCertificate K C' := by
  refine { component := N.component, diameter_bound := fun x => ?_ }
  obtain ⟨A⟩ := P.normalization M K x 0 le_rfl
  have hx : 0 < (K.flow.connection 0).scalarCurvature x := A.scale_eq ▸ A.scale_pos
  exact (N.diameter_bound x).trans_le
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx.le _))

theorem RepairedCanonicalNeighborhoodCertificate.mono_constant
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (N : RepairedCanonicalNeighborhoodCertificate K epsilon C) (hC : C ≤ C') :
    Nonempty (RepairedCanonicalNeighborhoodCertificate K epsilon C') := by
  refine ⟨{
    epsilon_pos := N.epsilon_pos
    constant_pos := N.constant_pos.trans_le hC
    compact_alternatives := ?_
  }⟩
  obtain ⟨hN⟩ := N.compact_alternatives
  cases hN with
  | round hr hq => exact ⟨.round hr hq⟩
  | compactSmall hc => exact ⟨.compactSmall (hc.mono_constant P hC)⟩
  | doubleCapped ht => exact ⟨.doubleCapped (ht.mono_constant hC)⟩

end PoincareConjecture
