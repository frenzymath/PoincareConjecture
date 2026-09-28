import PoincareConjecture.Proofs.M64.Mathlib.ConeTangentChord
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalChordBounds
import Mathlib.Analysis.Calculus.Deriv.Slope











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_constrained_minimizer_outgoing_tangent_mem
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    {gamma : ℝ → AnnulusCoordinates} {L : ℝ}
    (hc : ContinuousOn gamma (Icc 0 L)) (hconf : MapsTo gamma (Icc 0 L) K)
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma a → tau 1 = gamma b → MapsTo tau (Icc 0 1) K →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G tau 0 1)
    (H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (h0 : (0 : AnnulusCoordinates) ∈ H.source)
    (hH : ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source)
    (hHi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm H.target)
    (C : ConvexCone ℝ AnnulusCoordinates) (hC : IsClosed (C : Set AnnulusCoordinates))
    (hzero : (0 : AnnulusCoordinates) ∈ C)
    (hregion : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ K ↔ z ∈ C)
    {u : ℝ} (hu : u ∈ Ioo 0 L) (hpoint : gamma u = H 0)
    {v : AnnulusCoordinates}
    (hderiv : HasDerivWithinAt (fun r : ℝ => H.symm (gamma (u + r))) v (Ioi 0) 0) :
    v ∈ C ∧ -v ∈ C := by
  have hD : H.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hH.mdifferentiableOn (by simp), hHi.mdifferentiableOn (by simp)⟩
  obtain ⟨A, hA, _⟩ := G.exists_frozenPullbackEquiv (hD.mfderiv h0).injective
  let Q := C.map A.toLinearEquiv.toLinearMap
  have hQ : IsClosed (Q : Set AnnulusCoordinates) :=
    A.toHomeomorph.isClosedMap _ hC
  have hQzero : (0 : AnnulusCoordinates) ∈ Q := ⟨0, hzero, map_zero A⟩
  have hlimit : Tendsto (fun r : ℝ => r⁻¹ • H.symm (gamma (u + r)))
      (𝓝[>] 0) (𝓝 v) := by
    apply ((hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi.mpr le_rfl)).mp hderiv).congr'
    filter_upwards [] with r
    simp only [slope_def_module, sub_zero, add_zero, hpoint, H.left_inv h0]
  have hAlimit : Tendsto (fun r : ℝ => r⁻¹ • A (H.symm (gamma (u + r))))
      (𝓝[>] 0) (𝓝 (A v)) := by
    apply ((A.continuous.tendsto v).comp hlimit).congr'
    filter_upwards [] with r
    exact map_smul A r⁻¹ (H.symm (gamma (u + r)))
  obtain ⟨hvQ, hnegQ⟩ := m64ClosedCone_tangent_mem_and_neg_mem_of_chord_bounds
    Q hQ hQzero (x := fun r => A (H.symm (gamma (u - r)))) hAlimit (by
      intro theta htheta
      obtain ⟨epsilon, hepsilon, hbound⟩ :=
        m64Intrinsic_constrained_minimizer_local_chord_bounds G hc hconf hlip hmin
          H h0 hH hHi C.convex hregion A hA hu hpoint htheta
      refine ⟨epsilon, hepsilon, ?_⟩
      intro r hr he
      obtain ⟨hx, hy, hxn, hyn, hlower⟩ := hbound r hr he
      exact ⟨⟨_, hx, rfl⟩, ⟨_, hy, rfl⟩, hxn, hyn, by simpa only [map_sub] using hlower⟩)
  constructor
  · obtain ⟨z, hz, hzv⟩ := hvQ
    exact A.injective hzv ▸ hz
  · obtain ⟨z, hz, hzv⟩ := hnegQ
    have hzeq : z = -v := A.injective (by rw [map_neg]; exact hzv)
    exact hzeq ▸ hz

end PoincareConjecture
