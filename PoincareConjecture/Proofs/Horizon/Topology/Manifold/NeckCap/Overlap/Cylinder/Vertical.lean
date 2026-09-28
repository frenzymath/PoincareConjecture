import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.CylinderGluing

theorem vertical_mfderiv_bijective_at (h : RoundCylinderSpace → ℝ)
    {p : RoundCylinderSpace}
    (hh : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h p)
    {a : ℝ} (ha : a ≠ 0) (hderiv : HasDerivAt (fun t => h (p.1, t)) a p.2) :
    Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) p) := by
  let D : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] ℝ :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) h p
  let Q : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q => h (q, p.2)) p.1
  have hvertical (v : EuclideanSpace ℝ (Fin 2) × ℝ) : D v = Q v.1 + a * v.2 := by
    dsimp only [D, Q]
    erw [mfderiv_prod_eq_add_apply (hh.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, fderiv_eq_deriv_mul (𝕜 := ℝ), hderiv.deriv]
    rfl
  have htotal : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun z => (z.1, h z)) p =
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).prod D := by
    rw [mfderiv_prodMk mdifferentiableAt_fst (hh.mdifferentiableAt (by simp)), mfderiv_fst]
    rfl
  have hinj : Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) (fun z => (z.1, h z)) p) := by
    intro v w hvw
    rw [htotal] at hvw
    have hfirst := congrArg Prod.fst hvw
    change v.1 = w.1 at hfirst
    have hsecond : D v = D w := congrArg Prod.snd hvw
    rw [hvertical, hvertical, hfirst] at hsecond
    exact Prod.ext hfirst (mul_left_cancel₀ ha (add_left_cancel hsecond))
  let L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun z : RoundCylinderSpace => (z.1, h z)) p
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩

theorem vertical_isLocalDiffeomorphOn (h : RoundCylinderSpace → ℝ)
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hh : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ h U)
    (hderiv : ∀ p ∈ U, ∃ a : ℝ, a ≠ 0 ∧ HasDerivAt (fun t => h (p.1, t)) a p.2) :
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun z => (z.1, h z)) U := by
  let f : RoundCylinderSpace → RoundCylinderSpace := fun z => (z.1, h z)
  have hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f U :=
    contMDiffOn_fst.prodMk hh
  have hbij (x : RoundCylinderSpace) (hx : x ∈ U) : Function.Bijective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f x) := by
    obtain ⟨a, ha, hd⟩ := hderiv x hx
    exact vertical_mfderiv_bijective_at h (hh.contMDiffAt (hU.mem_nhds hx)) ha hd
  let E := EuclideanSpace ℝ (Fin 2) × ℝ
  let : ChartedSpace E RoundCylinderSpace := prodChartedSpace _ _ _ _
  let : IsManifold 𝓘(ℝ, E) ∞ RoundCylinderSpace := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) UnitTwoSphere ℝ
  rw [← modelWithCornersSelf_prod] at hf hbij ⊢
  intro x
  let c := chartAt E (x : RoundCylinderSpace)
  let d := chartAt E (f x)
  let F := writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) (x : RoundCylinderSpace) f
  have hfx := hf.contMDiffAt (hU.mem_nhds x.property)
  have hF : ContDiffAt ℝ ∞ F (c x) := by
    have hs := (contMDiffAt_iff.mp hfx).2
    simp only [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] at hs
    convert hs using 1 <;> rfl
  have hdiff : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x = fderiv ℝ F (c x) := by
    rw [mfderiv, if_pos (hfx.mdifferentiableAt (by simp))]
    simp [F, c]
  have hFbij : Function.Bijective (fderiv ℝ F (c x)) := by
    rw [← hdiff]
    exact hbij x x.property
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ F (c x))
    (LinearMap.ker_eq_bot.mpr hFbij.1) (LinearMap.range_eq_top.mpr hFbij.2)
  have hdF : HasFDerivAt F A.toContinuousLinearMap (c x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  let Q := hF.toOpenPartialHomeomorph F hdF (by simp)
  let H := (c.trans (Q.trans d.symm)).restr (U ∩ f ⁻¹' d.source)
  have hFc (z : RoundCylinderSpace) (hz : z ∈ c.source) : F (c z) = d (f z) := by
    change d (f (c.symm (c z))) = d (f z)
    rw [c.left_inv hz]
  have hxH : (x : RoundCylinderSpace) ∈ H.source := by
    rw [OpenPartialHomeomorph.restr_source, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source]
    refine ⟨⟨mem_chart_source _ _, ⟨hF.mem_toOpenPartialHomeomorph_source hdF (by simp),
      ?_⟩⟩, ?_⟩
    · change F (c x) ∈ d.target
      rw [hFc x (mem_chart_source _ _)]
      exact d.map_source (mem_chart_source _ _)
    · apply mem_interior_iff_mem_nhds.mpr
      exact inter_mem (hU.mem_nhds x.property)
        (hfx.continuousAt.preimage_mem_nhds
          (d.open_source.mem_nhds (mem_chart_source _ _)))
  have hsub : H.source ⊆ U := fun z hz => (interior_subset hz.2).1
  have heq : EqOn f H H.source := by
    intro z hz
    have hsrc : f z ∈ d.source := (interior_subset hz.2).2
    change f z = d.symm (F (c z))
    rw [hFc z hz.1.1, d.left_inv hsrc]
  have hH : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ H H.source :=
    (hf.mono hsub).congr heq.symm
  have hHi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ H.symm H.target := by
    intro y hy
    have hz := H.symm.map_source hy
    have hfy : f (H.symm y) = y := (heq hz).trans (H.right_inv hy)
    have hleft : ∀ᶠ z in 𝓝 (H.symm y), H.symm (f z) = z := by
      filter_upwards [H.open_source.mem_nhds hz] with z hzs
      rw [heq hzs]
      exact H.left_inv hzs
    have hs := Poincare.Geometry.Manifold.contMDiffAt_of_local_left_inverse_modelSpaces
      (hf.contMDiffAt (hU.mem_nhds (hsub hz))) (hbij _ (hsub hz)) hleft
    rw [hfy] at hs
    exact hs.contMDiffWithinAt
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) RoundCylinderSpace RoundCylinderSpace ∞ := {
    toPartialEquiv := H.toPartialEquiv
    open_source := H.open_source
    open_target := H.open_target
    contMDiffOn_toFun := hH
    contMDiffOn_invFun := hHi }
  exact ⟨Φ, hxH, heq⟩

end PoincareConjecture.CylinderGluing
