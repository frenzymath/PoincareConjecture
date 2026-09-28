import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InteriorUnitSpeed
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactGeodesicContinuation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_compact_geodesic_right_derivative_unit
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {a b : ℝ} (hab : a < b) {q : ℝ → AnnulusCoordinates}
    (hgeo : G.IsGeodesicOn q (Ioo a b)) (hmap : MapsTo q (Ioo a b) K)
    (hc : ContinuousWithinAt q (Ici a) a)
    (hunit : ∀ t ∈ Ioo a b, G.tangentNorm (q t) (deriv q t) = 1)
    {v : AnnulusCoordinates} (hv : HasDerivWithinAt q v (Ioi a) a) :
    G.tangentNorm (q a) v = 1 := by
  obtain ⟨epsilon, hepsilon, eta, heq, heta⟩ :=
    m64Intrinsic_compact_geodesic_left_extension G hK hab hgeo hmap hc
  have haJ : a ∈ Ioo (a - epsilon) b := ⟨by linarith, hab⟩
  have hd : HasDerivAt eta (deriv eta a) a :=
    (contMDiffAt_iff_contDiffAt.mp (heta.contMDiffAt haJ)).differentiableAt
      (by simp) |>.hasDerivAt
  have hdq : HasDerivWithinAt q (deriv eta a) (Ioi a) a := by
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [Ioo_mem_nhdsGT hab] with t ht
      exact (heq ⟨ht.1.le, ht.2⟩).symm
    · exact (heq ⟨le_rfl, hab⟩).symm
  have hveq : v = deriv eta a :=
    (hv.derivWithin (uniqueDiffWithinAt_Ioi a)).symm.trans
      (hdq.derivWithin (uniqueDiffWithinAt_Ioi a))
  obtain ⟨C, hC⟩ := heta.exists_constant_tangentNorm (by linarith : a - epsilon < b)
  have hconstant (t : ℝ) (ht : t ∈ Ioo (a - epsilon) b) :
      G.tangentNorm (eta t) (deriv eta t) = C := by
    have hh := hC t ht
    change G.tangentNorm (eta t) (curveVelocity (n := 2) eta t) = C at hh
    rwa [m64Intrinsic_curveVelocity_eq_deriv] at hh
  let c := (a + b) / 2
  have hcI : c ∈ Ioo a b := by dsimp only [c]; constructor <;> linarith
  have hnear : eta =ᶠ[𝓝 c] q := by
    filter_upwards [isOpen_Ioo.mem_nhds hcI] with t ht
    exact heq ⟨ht.1.le, ht.2⟩
  have hCunit : (C : ℝ) = 1 := by
    rw [← hconstant c ⟨by linarith [hcI.1], hcI.2⟩,
      hnear.self_of_nhds, hnear.deriv_eq]
    exact hunit c hcI
  rw [hveq, ← heq ⟨le_rfl, hab⟩]
  exact (hconstant a haJ).trans hCunit

end PoincareConjecture
