import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.PolarCoordinates

/-!
# The actual differential of the end coordinates

Morgan-Tian Definition 12.1 and Lemma 12.2, printed pp. 293-295.
The sphere inclusion has tangent image orthogonal to its radius. The
actual manifold derivative of the end coordinate is the sum of its
spherical and radial parts, as needed by the frozen pullback identity.
-/

set_option autoImplicit false

open scoped Manifold ContDiff InnerProductSpace

namespace PoincareMT.M34

/-- Sphere tangent vectors are Euclidean-orthogonal to the radial unit
vector, for the inclusion in the frozen cylinder metric
(Definition 12.1, pp. 293-294). -/
theorem capSphere_tangent_orthogonal (u : UnitTwoSphere) (v : TangentSpace (𝓡 2) u) :
    inner ℝ (u : StandardCapSpace)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) u v) = 0 := by
  have : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hmem : mvfderiv (𝓡 2) (fun q : UnitTwoSphere => q.1) u v ∈
      (mvfderiv (𝓡 2) (fun q : UnitTwoSphere => q.1) u).range := ⟨v, rfl⟩
  rw [range_mvfderiv_subtypeVal] at hmem
  convert! Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem using 1

set_option backward.isDefEq.respectTransparency false in
/-- The frozen manifold derivative of the polar coordinate map is the
sum of its angular and radial terms (Definition 12.1, pp. 293-294). -/
theorem capCylinderCoordinate_mfderiv (R : ℝ) (z : StandardCylinderSpace)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (capCylinderCoordinate R) z v =
      (R + z.2) • mvfderiv (𝓡 2) (fun q : UnitTwoSphere => q.1) z.1 v.1 +
        v.2 • (z.1 : StandardCapSpace) := by
  have : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hsphere : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q : UnitTwoSphere => q.1) :=
    contMDiff_coe_sphere
  have hscalar : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : StandardCylinderSpace => R + q.2) := contMDiff_const.add contMDiff_snd
  have hangular : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun q : StandardCylinderSpace => q.1.1) := hsphere.comp contMDiff_fst
  have hds : mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun q : StandardCylinderSpace => R + q.2) z v = v.2 := by
    rw [mvfderiv_fun_add mdifferentiableAt_const mdifferentiableAt_snd, mvfderiv_const]
    simp only [zero_add]
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd z v = v.2
    rw [mfderiv_snd]
    rfl
  have hda : mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun q : StandardCylinderSpace => q.1.1) z v =
        mvfderiv (𝓡 2) (fun q : UnitTwoSphere => q.1) z.1 v.1 := by
    have hcomp : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        ((fun q : UnitTwoSphere => q.1) ∘ Prod.fst) z =
          (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) z.1).comp
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 2) Prod.fst z) :=
      mfderiv_comp z (hsphere.mdifferentiable (by simp) z.1) mdifferentiableAt_fst
    have happ := congrArg (fun L => L v) hcomp
    simp only [mfderiv_fst] at happ
    convert! happ using 1
  change mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (fun q : StandardCylinderSpace => (R + q.2) • q.1.1) z v = _
  rw [mvfderiv_fun_smul (hscalar.mdifferentiable (by simp) z)
    (hangular.mdifferentiable (by simp) z)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, hds, hda]

end PoincareMT.M34
