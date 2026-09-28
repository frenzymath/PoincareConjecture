import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNorthChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.TransverseSphereCollar
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D




theorem sphere_horizontal_mvfderiv_bijective
    (p : UnitTwoSphere) (hp : (heightCoordinates (p : E3)).2 ≠ 0) :
    Function.Bijective (mvfderiv (𝓡 2)
      (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).1) p) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) p) := by
    change FiniteDimensional ℝ E2
    infer_instance
  let X : UnitTwoSphere → E2 := fun q => (heightCoordinates (q : E3)).1
  let B : TangentSpace (𝓡 2) p →L[ℝ] E3 :=
    mvfderiv (𝓡 2) (fun q : UnitTwoSphere => (q : E3)) p
  let L : E3 →L[ℝ] E2 :=
    (ContinuousLinearMap.fst ℝ E2 ℝ).comp heightCoordinates.toContinuousLinearMap
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
      (fun q : UnitTwoSphere => (q : E3)) := contMDiff_coe_sphere
  have hd := L.hasFDerivAt.hasMFDerivAt.comp p
    (hi.mdifferentiable (by simp) p).hasMFDerivAt
  have hX (v : TangentSpace (𝓡 2) p) :
      mvfderiv (𝓡 2) X p v = (heightCoordinates (B v)).1 := by
    exact congrArg (fun F => F v) hd.mfderiv
  have hB : B.range = (ℝ ∙ (p : E3))ᗮ := range_mvfderiv_subtypeVal p
  have hinj : Function.Injective (mvfderiv (𝓡 2) X p) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hfst : (heightCoordinates (B v)).1 = 0 := (hX v).symm.trans hv
    have hperp : B v ∈ (ℝ ∙ (p : E3))ᗮ := by
      rw [← hB]
      exact ⟨v, rfl⟩
    have hinner : ⟪(p : E3), B v⟫_ℝ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp hperp
    have h0 : B v 0 = 0 := congrArg (fun x : E2 => x 0) hfst
    have h1 : B v 1 = 0 := congrArg (fun x : E2 => x 1) hfst
    have hcoord : ⟪(p : E3), B v⟫_ℝ =
        (heightCoordinates (p : E3)).2 * (heightCoordinates (B v)).2 := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
        dotProduct, Fin.sum_univ_three, h0, h1, zero_mul, zero_add,
        heightCoordinates_snd_apply]
      ring
    have hsnd : (heightCoordinates (B v)).2 = 0 :=
      (mul_eq_zero.mp (hcoord.symm.trans hinner)).resolve_left hp
    have hBv : B v = 0 := by
      apply heightCoordinates.injective
      exact (Prod.ext hfst hsnd).trans heightCoordinates.map_zero.symm
    apply injective_mvfderiv_subtypeVal_sphere p
    simpa only [map_zero] using hBv
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) p) = Module.finrank ℝ E2 := rfl
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mvfderiv (𝓡 2) X p).toLinearMap) hdim).mp hinj⟩




theorem north_collar_candidate_regular
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (Q : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere)
    (hQ : ContMDiffOn (𝓡 2) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ Q.symm Q.target) :
    let A := fun z : UnitTwoSphere × ℝ => psi (Q z.1, z.2)
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ A
      (Q.source ×ˢ Ioo (-1) 1) ∧
      ∀ p ∈ Q.source,
        Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) A (p, 0)) := by
  let QP := Q.prod (OpenPartialHomeomorph.refl ℝ)
  have hQP : QP.MDifferentiable ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) :=
    ⟨(hQ.prodMap contMDiffOn_id).mdifferentiableOn (by simp),
      (hQi.prodMap contMDiffOn_id).mdifferentiableOn (by simp)⟩
  refine ⟨hpsi.1.comp (hQ.prodMap contMDiffOn_id)
    (fun z hz => ⟨mem_univ _, hz.2⟩), ?_⟩
  intro p hp
  have hpoint : (Q p, (0 : ℝ)) ∈
      (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (UnitTwoSphere × ℝ)) :=
    ⟨mem_univ _, by norm_num⟩
  have hpd := (hpsi.1.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hpoint)).mdifferentiableAt (by simp)
  have hQpoint : (p, (0 : ℝ)) ∈ QP.source := ⟨hp, mem_univ _⟩
  have hpi := hpsi.2.2 (Q p, 0) hpoint
  let : FiniteDimensional ℝ
      (TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Q p, (0 : ℝ))) := by
    change FiniteDimensional ℝ (E2 × ℝ)
    infer_instance
  have hdim : Module.finrank ℝ
      (TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) (Q p, (0 : ℝ))) =
        Module.finrank ℝ E3 := by
    change Module.finrank ℝ (E2 × ℝ) = Module.finrank ℝ E3
    simp [E2, E3, Module.finrank_prod]
  have hpb : Function.Bijective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) psi (Q p, 0)) :=
    ⟨hpi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) psi (Q p, 0)).toLinearMap)
      hdim).mp hpi⟩
  change Function.Bijective
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) (psi ∘ QP) (p, 0))
  rw [mfderiv_comp (p, 0) hpd (hQP.mdifferentiableAt hQpoint)]
  exact hpb.comp (hQP.mfderiv_bijective hQpoint)




theorem flat_tube_candidate_regular
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target) (z0 : ℝ) :
    let A := fun z : UnitTwoSphere × ℝ =>
      T ((heightCoordinates (z.1 : E3)).1, z0 + z.2)
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ A ∧
      ∀ p : UnitTwoSphere, (heightCoordinates (p : E3)).2 < 0 →
        Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) A (p, 0)) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let X : UnitTwoSphere → E2 := fun p => (heightCoordinates (p : E3)).1
  let G : UnitTwoSphere × ℝ → E2 × ℝ := fun z => (X z.1, z0 + z.2)
  have hX : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞ X :=
    contDiff_fst.contMDiff.comp
      (heightCoordinates.contDiff.contMDiff.comp contMDiff_coe_sphere)
  have hz : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => z0 + s) :=
    contMDiff_const.add contMDiff_id
  have hG : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2 × ℝ) ∞ G :=
    (hX.comp contMDiff_fst).prodMk_space (contMDiff_const.add contMDiff_snd)
  have hGmem (z : UnitTwoSphere × ℝ) : G z ∈ T.source := by
    apply hsource
    refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_univ _⟩
    have hs := sphere_height_coordinates_sq z.1
    change ‖X z.1‖ ^ 2 + (heightCoordinates (z.1 : E3)).2 ^ 2 = 1 at hs
    nlinarith [sq_nonneg (heightCoordinates (z.1 : E3)).2,
      sq_nonneg (‖X z.1‖ - 1), norm_nonneg (X z.1)]
  have hTd : T.MDifferentiable 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E3) :=
    ⟨hT.contMDiffOn.mdifferentiableOn (by simp),
      hTi.contMDiffOn.mdifferentiableOn (by simp)⟩
  refine ⟨hT.contMDiffOn.comp_contMDiff hG hGmem, ?_⟩
  intro p hp
  have hXb := sphere_horizontal_mvfderiv_bijective p hp.ne
  have hzd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => z0 + s) 0 =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderiv_eq_fderiv]
    have hd : HasFDerivAt (fun s : ℝ => z0 + s)
        (0 + ContinuousLinearMap.id ℝ ℝ) 0 :=
      (hasFDerivAt_const z0 (0 : ℝ)).add (hasFDerivAt_id (0 : ℝ))
    have hd' : fderiv ℝ (fun s : ℝ => z0 + s) 0 = ContinuousLinearMap.id ℝ ℝ := by
      simpa only [zero_add] using hd.fderiv
    apply ContinuousLinearMap.ext
    intro s
    exact congrArg (fun F : ℝ →L[ℝ] ℝ => F s) hd'
  have hGbprod : Function.Bijective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, E2).prod 𝓘(ℝ, ℝ))
        (Prod.map X (fun s : ℝ => z0 + s)) (p, 0)) := by
    rw [mfderiv_prodMap (hX.mdifferentiable (by simp) p)
      (hz.mdifferentiable (by simp) 0), hzd]
    constructor
    · rintro ⟨v, s⟩ ⟨v', s'⟩ he
      have he' : (mvfderiv (𝓡 2) X p v, s) = (mvfderiv (𝓡 2) X p v', s') := he
      have hs : s = s' := congrArg (fun y : E2 × ℝ => y.2) he'
      exact Prod.ext (hXb.1 (congrArg Prod.fst he')) hs
    · rintro ⟨x, s⟩
      obtain ⟨v, hv⟩ := hXb.2 x
      exact ⟨(v, s), Prod.ext hv rfl⟩
  have hGb : Function.Bijective
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2 × ℝ) G (p, 0)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    rw [show G = Prod.map X (fun s : ℝ => z0 + s) from rfl]
    exact hGbprod
  change Function.Bijective
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) (T ∘ G) (p, 0))
  rw [mfderiv_comp (p, 0) (hTd.mdifferentiableAt (hGmem (p, 0)))
    (hG.mdifferentiable (by simp) (p, 0))]
  exact (hTd.mfderiv_bijective (hGmem (p, 0))).comp hGb

end PoincareConjecture.M25.Topology3D
