import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.CapGeometry.InitialAxialPatch
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Neck.Geometry.NeckCharts
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.SphereCoordinates

/-!
# The actual differential of the initial axial normalization

Morgan-Tian Theorem 12.32, pp. 326-327. The time-independent neck
map has literal differential `(v_sphere, c*v_axis)`. This identity
records the true metric pullback before any finite-jet estimate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35

/-- The actual product-manifold derivative of the axial dilation. -/
theorem cylinderAxialDilation_mfderiv (c : ℝ) (hc : 0 < c)
    (z : StandardCylinderSpace)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderAxialDilation c hc) z v = (v.1, c * v.2) := by
  have hd : HasFDerivAt (fun r : ℝ => c * r)
      (c • ContinuousLinearMap.id ℝ ℝ) z.2 := by
    simpa only [smul_eq_mul] using! (hasFDerivAt_id z.2).const_smul c
  have haxis := hd.hasMFDerivAt.comp z
    (hasMFDerivAt_snd (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) z)
  have hprod := (hasMFDerivAt_fst (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (x := z)).prodMk haxis
  have h := congrArg
    (fun L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
        (EuclideanSpace ℝ (Fin 2) × ℝ) => L v) hprod.mfderiv
  convert! h using 1

/-- The actual normalized patch pulls the original metric back
with its displayed scalar normalization and axial differential. -/
theorem initial_axial_patch_pullback
    (g : RiemannianMetric 3 StandardCapSpace) {length : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch length x) (c l : ℝ) (hc : 0 < c) (hl : 0 < l)
    (hcl : c * l ≤ length) (z : StandardCylinderSpace) (hz : z.2 ∈ Ioo (-l) l)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    roundCylinderPullback g (N.axialRescale c l hc hl hcl).coordinate z v w =
      roundCylinderPullback g N.coordinate (z.1, c * z.2)
        (v.1, c * v.2) (w.1, c * w.2) := by
  let e := cylinderAxialDilation c hc
  have hin : (e z).2 ∈ Ioo (-length) length := by
    change -length < c * z.2 ∧ c * z.2 < length
    have hlo := mul_lt_mul_of_pos_left hz.1 hc
    have hhi := mul_lt_mul_of_pos_left hz.2 hc
    constructor <;> nlinarith only [hlo, hhi, hcl]
  have hN := (N.coordinate_smooth (e z) ⟨mem_univ _, hin⟩).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hin⟩)
  have hderiv (u : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (N.axialRescale c l hc hl hcl).coordinate z u =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate (z.1, c * z.2)
        (u.1, c * u.2) := by
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (N.coordinate ∘ e) z u = _
    rw [mfderiv_comp_apply z (hN.mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiable (by simp) z)]
    rw [cylinderAxialDilation_mfderiv]
    rfl
  simpa only [roundCylinderPullback] using!
    congrArg₂ (fun a b => g.inner ((N.axialRescale c l hc hl hcl).coordinate z) a b)
      (hderiv v) (hderiv w)

end PoincareMT.M35
