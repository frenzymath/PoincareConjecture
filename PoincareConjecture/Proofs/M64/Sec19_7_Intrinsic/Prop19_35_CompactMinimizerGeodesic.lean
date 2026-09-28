import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AffineCollisionBoundaryAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactGeodesicRepresentative
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InteriorUnitSpeed





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold ENNReal

namespace PoincareConjecture







theorem m64Intrinsic_constrained_minimizer_smooth_unit_geodesic
    (G : RiemannianMetric 2 AnnulusCoordinates) {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn gamma (Icc 0 T)) (hinside : MapsTo gamma (Ioo 0 T) U)
    (hlip : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma s → tau 1 = gamma t → MapsTo tau (Icc 0 1) (closure U) →
          ENNReal.ofReal (t - s) ≤ m64IntrinsicCurveVariation G tau 0 1) :
    ∃ eta : ℝ → AnnulusCoordinates,
      ContDiff ℝ ∞ eta ∧ EqOn eta gamma (Icc 0 T) ∧
      G.IsGeodesicOn eta (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, G.inner (eta t) (deriv eta t) (deriv eta t) = 1) ∧
      (∀ t ∈ Icc 0 T, deriv eta t ≠ 0) ∧
      HasDerivWithinAt gamma (deriv eta 0) (Ioi 0) 0 ∧
      HasDerivWithinAt gamma (deriv eta T) (Iio T) T := by
  obtain ⟨hgeo, _⟩ :=
    m64Intrinsic_constrained_minimizer_geodesic_of_open_confinement
      G hU hcompact hinside hlip hmin
  obtain ⟨eta, heta, heq, hegeo, hd0, hdT⟩ :=
    m64Intrinsic_compact_geodesic_smooth_representative G hcompact hT hc hgeo
      (fun t ht => subset_closure (hinside ht))
  have hm : T / 2 ∈ Ioo 0 T := ⟨by linarith, by linarith⟩
  have hmcc := Ioo_subset_Icc_self hm
  have hUi : U ⊆ interior (closure U) := by
    calc
      U = interior U := hU.interior_eq.symm
      _ ⊆ interior (closure U) := interior_mono subset_closure
  have hmid : G.tangentNorm (eta (T / 2)) (deriv eta (T / 2)) = 1 := by
    have hnear : eta =ᶠ[𝓝 (T / 2)] gamma := by
      filter_upwards [isOpen_Ioo.mem_nhds hm] with t ht
      exact heq (Ioo_subset_Icc_self ht)
    rw [heq hmcc, hnear.deriv_eq]
    exact m64Intrinsic_constrained_minimizer_interior_unit_speed
      G hcompact hlip hmin hm (hUi (hinside hm))
  have hspeed (t : ℝ) (ht : t ∈ Icc 0 T) :
      G.tangentNorm (eta t) (deriv eta t) = 1 := by
    have hd (s : ℝ) (hs : s ∈ Icc 0 T) :
        HasDerivWithinAt (fun x => G.tangentNorm (eta x) (deriv eta x)) 0 (Icc 0 T) s := by
      have hh := hegeo.hasDerivAt_tangentNorm_zero hs
      change HasDerivAt
        (fun x => G.tangentNorm (eta x) (curveVelocity (n := 2) eta x)) 0 s at hh
      simp_rw [m64Intrinsic_curveVelocity_eq_deriv] at hh
      exact hh.hasDerivWithinAt
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (show ∀ s ∈ Icc 0 T, ‖(0 : ℝ)‖ ≤ 0 from fun _ _ => by simp)
      (convex_Icc 0 T) hmcc ht
    have hequal : G.tangentNorm (eta t) (deriv eta t) =
        G.tangentNorm (eta (T / 2)) (deriv eta (T / 2)) := by
      simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh
    exact hequal.trans hmid
  have hreg (t : ℝ) (ht : t ∈ Icc 0 T) : deriv eta t ≠ 0 := by
    intro hz
    have hu := hspeed t ht
    simp only [hz, RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero] at hu
    exact zero_ne_one hu
  refine ⟨eta, heta, heq, hegeo, ?_, hreg, hd0, hdT⟩
  intro t ht
  have hsq : G.tangentNorm (eta t) (deriv eta t) ^ 2 =
      G.inner (eta t) (deriv eta t) (deriv eta t) :=
    Real.sq_sqrt (G.pos (eta t) (deriv eta t) (hreg t ht)).le
  rw [hspeed t ht, one_pow] at hsq
  exact hsq.symm

end PoincareConjecture
