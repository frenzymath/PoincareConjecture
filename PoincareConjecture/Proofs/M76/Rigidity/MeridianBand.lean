import PoincareConjecture.Proofs.M76.Rigidity.MeridianCut
import PoincareConjecture.Proofs.M76.Rigidity.MeridianBandCarrier









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "I" => Icc (-1 : ℝ) 1
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < p) := ⟨by norm_num⟩



theorem continuous_hamiltonMeridianCutAmbientMap :
    Continuous hamiltonMeridianCutAmbientMap :=
  continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp
    (continuous_pi fun _ : Fin 1 => continuous_snd))



theorem injOn_hamiltonMeridianBand :
    InjOn hamiltonMeridianCutAmbientMap (Q ×ˢ I) := by
  intro z hz w hw heq
  have hfst : z.1 = w.1 := congrArg (fun x : X => x.1) heq
  have hsnd := congrArg (fun x : X => hamiltonSolidTorusCircleEquiv x.2) heq
  change (z.2 : AddCircle p) = (w.2 : AddCircle p) at hsnd
  have hzs : z.2 ∈ (AddCircle.shortArcQuotient p 2).source := by
    rw [AddCircle.shortArcQuotient_source p (by norm_num)]
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hws : w.2 ∈ (AddCircle.shortArcQuotient p 2).source := by
    rw [AddCircle.shortArcQuotient_source p (by norm_num)]
    exact ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩
  exact Prod.ext hfst ((AddCircle.shortArcQuotient p 2).injOn hzs hws hsnd)



theorem mapsTo_hamiltonMeridianBand_frontier :
    MapsTo hamiltonMeridianCutAmbientMap (Q ×ˢ I) (frontier R) := by
  intro z hz
  rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
  exact ⟨hz.1, mem_univ _⟩



theorem hamiltonMeridianBand_zero (z : V2) :
    hamiltonMeridianCutAmbientMap (z, 0) = hamiltonStandardMeridianMap L z := rfl




theorem isOpen_hamiltonMeridianBand_image :
    IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      (hamiltonMeridianCutAmbientMap '' (Q ×ˢ Ioo (-1 : ℝ) 1))) := by
  let U : Set T := hamiltonSolidTorusCircleEquiv ⁻¹'
    (AddCircle.shortArcQuotient p 1).target
  have hU : IsOpen U := (AddCircle.shortArcQuotient p 1).open_target.preimage
    hamiltonSolidTorusCircleEquiv.continuous
  have heq : (Subtype.val : frontier R → X) ⁻¹'
      (hamiltonMeridianCutAmbientMap '' (Q ×ˢ Ioo (-1 : ℝ) 1)) =
      (fun y : frontier R => (y : X).2) ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      change hamiltonSolidTorusCircleEquiv (y : X).2 ∈
        (AddCircle.shortArcQuotient p 1).target
      rw [AddCircle.shortArcQuotient_target p (by norm_num)]
      refine ⟨z.2, hz.2, ?_⟩
      exact congrArg (fun x : X => hamiltonSolidTorusCircleEquiv x.2) hzy
    · intro hy
      change hamiltonSolidTorusCircleEquiv (y : X).2 ∈
        (AddCircle.shortArcQuotient p 1).target at hy
      rw [AddCircle.shortArcQuotient_target p (by norm_num)] at hy
      obtain ⟨t, ht, hty⟩ := hy
      have hyQ : (y : X).1 ∈ Q := by
        have h : (y : X) ∈ frontier (latticeHandleDomain (Fin 2) (Fin 1) L) := y.property
        change (y : X) ∈ frontier (closedBall (0 : V2) 1 ×ˢ (univ : Set T)) at h
        rw [frontier_prod_univ_eq,
          frontier_closedBall _ one_ne_zero] at h
        exact h.1
      refine ⟨((y : X).1, t), ⟨hyQ, ht⟩, Prod.ext rfl ?_⟩
      exact hamiltonSolidTorusCircleEquiv.injective hty
  rw [heq]
  exact hU.preimage (continuous_snd.comp continuous_subtype_val)



theorem StandardLatticeHandleAtlas.polyhedralPL_meridianBand
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) :
    PolyhedralPLInCharts d hamiltonMeridianCutAmbientMap (Q ×ˢ I) := by
  obtain ⟨K, hK, hKI⟩ := exists_finite_hamiltonMeridianBand
    (a := (-1 : ℝ)) (b := 1) (by norm_num)
  let a : (V2 × ℝ) →ᴬ[ℝ] ((Fin 2 ⊕ Fin 1) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 2) (Fin 1)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((ContinuousLinearMap.fst ℝ V2 ℝ).prod
          (ContinuousLinearMap.pi fun _ : Fin 1 =>
            ContinuousLinearMap.snd ℝ V2 ℝ)).toContinuousAffineMap
  have ha : FinitePiecewiseAffineOn a (Q ×ˢ I) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine a⟩
  exact hd.polyhedralPL_projection ha

end PoincareConjecture.M76
