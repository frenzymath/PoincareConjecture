import PoincareConjecture.Proofs.M76.Rigidity.MeridianBicollar
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < p) := ⟨by norm_num⟩




noncomputable def hamiltonMeridianCutMap : C(D × ℝ, H) :=
  ⟨fun z => (z.1, hamiltonSolidTorusCircleEquiv.symm (z.2 : AddCircle p)),
    continuous_fst.prodMk (hamiltonSolidTorusCircleEquiv.symm.continuous.comp
      ((AddCircle.continuous_mk' p).comp continuous_snd))⟩



theorem hamiltonMeridianCutMap_apply (x : D) (t : ℝ) :
    hamiltonMeridianCutMap (x, t) =
      (x, QuotientAddGroup.mk (fun _ : Fin 1 => t)) := by
  change (x, hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p)) = _
  rw [hamiltonSolidTorusCircleEquiv_symm_coe]



theorem hamiltonMeridianCutMap_zero (x : D) :
    hamiltonMeridianCutMap (x, 0) = hamiltonStandardMeridian L x := by
  rw [hamiltonMeridianCutMap_apply]
  rfl



theorem hamiltonMeridianCutMap_period (x : D) :
    hamiltonMeridianCutMap (x, p) = hamiltonStandardMeridian L x := by
  change (x, hamiltonSolidTorusCircleEquiv.symm ((p : ℝ) : AddCircle p)) = (x, 0)
  rw [AddCircle.coe_period]
  exact Prod.ext rfl (hamiltonSolidTorusCircleEquiv_symm_coe 0)



theorem hamiltonMeridianCutMap_image :
    hamiltonMeridianCutMap '' (univ ×ˢ Icc 0 p) = univ := by
  ext z
  constructor
  · intro _
    exact mem_univ _
  · intro _
    obtain ⟨t, ht, he⟩ := AddCircle.eq_coe_Ico (hamiltonSolidTorusCircleEquiv z.2)
    refine ⟨(z.1, t), ⟨mem_univ _, ht.1, ht.2.le⟩, ?_⟩
    change (z.1, hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p)) = z
    rw [he, hamiltonSolidTorusCircleEquiv.symm_apply_apply]




theorem hamiltonMeridianCutMap_preimage_boundary :
    hamiltonMeridianCutMap ⁻¹' latticeHandleBoundary (Fin 2) (Fin 1) L =
      {x : D | ‖(x : V2)‖ = 1} ×ˢ univ := by
  ext z
  rfl



theorem hamiltonMeridianCutMap_mem_meridian (x : D) {t : ℝ}
    (ht : t ∈ Icc 0 p) :
    hamiltonMeridianCutMap (x, t) ∈ hamiltonStandardMeridianSet L ↔
      t = 0 ∨ t = p := by
  change (True ∧ hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p) = 0) ↔ _
  rw [true_and]
  have hzero : hamiltonSolidTorusCircleEquiv.symm (0 : AddCircle p) = 0 :=
    hamiltonSolidTorusCircleEquiv_symm_coe 0
  rw [← hzero, hamiltonSolidTorusCircleEquiv.symm.injective.eq_iff]
  exact AddCircle.coe_eq_zero_iff_endpoints ht



theorem hamiltonMeridianCutMap_eq_iff (x y : D) {t u : ℝ}
    (ht : t ∈ Icc 0 p) (hu : u ∈ Icc 0 p) :
    hamiltonMeridianCutMap (x, t) = hamiltonMeridianCutMap (y, u) ↔
      x = y ∧ (t = u ∨ (t = 0 ∧ u = p) ∨ (t = p ∧ u = 0)) := by
  change (x, hamiltonSolidTorusCircleEquiv.symm (t : AddCircle p)) =
    (y, hamiltonSolidTorusCircleEquiv.symm (u : AddCircle p)) ↔ _
  rw [Prod.mk.injEq, hamiltonSolidTorusCircleEquiv.symm.injective.eq_iff,
    AddCircle.coe_eq_coe_iff_eq_or_endpoints ht hu]




noncomputable def hamiltonMeridianOpenCut : OpenPartialHomeomorph (D × ℝ) H :=
  (OpenPartialHomeomorph.refl D).prod
    ((AddCircle.openPartialHomeomorphCoe p 0).trans
      hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph)



theorem hamiltonMeridianOpenCut_source :
    hamiltonMeridianOpenCut.source = univ ×ˢ Ioo 0 p := by
  change univ ×ˢ ((AddCircle.openPartialHomeomorphCoe p 0).trans
    hamiltonSolidTorusCircleEquiv.symm.toOpenPartialHomeomorph).source = _
  rw [OpenPartialHomeomorph.trans_source]
  change univ ×ˢ (Ioo 0 (0 + p) ∩
    (AddCircle.openPartialHomeomorphCoe p 0) ⁻¹' univ) = _
  rw [preimage_univ, inter_univ, zero_add]



theorem hamiltonMeridianOpenCut_target :
    hamiltonMeridianOpenCut.target = (hamiltonStandardMeridianSet L)ᶜ := by
  ext z
  change (True ∧ (True ∧ hamiltonSolidTorusCircleEquiv z.2 ∉
    {(0 : AddCircle p)})) ↔ ¬(True ∧ z.2 = 0)
  simp only [true_and, mem_singleton_iff]
  constructor
  · intro h hz
    apply h
    rw [hz]
    rfl
  · intro h hz
    apply h
    apply hamiltonSolidTorusCircleEquiv.injective
    exact hz



theorem hamiltonMeridianOpenCut_apply (z : D × ℝ) :
    hamiltonMeridianOpenCut z = hamiltonMeridianCutMap z := rfl




theorem hamiltonMeridianCut_ballPair :
    IsFinitePLBallPair (V2 × ℝ) (D ×ˢ Icc 0 p)
      ((sphere (0 : V2) 1 ×ˢ Icc 0 p) ∪ (D ×ˢ {(0 : ℝ), p})) :=
  isFinitePLBallPair_unit_cube.prod (isFinitePLBallPair_Icc (by norm_num))



def hamiltonMeridianCutAmbientMap (z : V2 × ℝ) :
    LatticeHandleAmbient (Fin 2) (Fin 1) L :=
  (z.1, QuotientAddGroup.mk (fun _ : Fin 1 => z.2))



theorem hamiltonMeridianCutMap_ambient_apply (x : D) (t : ℝ) :
    (((hamiltonMeridianCutMap (x, t)).1 : V2),
      (hamiltonMeridianCutMap (x, t)).2) =
        hamiltonMeridianCutAmbientMap (x, t) := by
  rw [hamiltonMeridianCutMap_apply]
  rfl




theorem StandardLatticeHandleAtlas.polyhedralPL_meridianCut
    {β : Type*}
    {d : β → OpenPartialHomeomorph
      (LatticeHandleAmbient (Fin 2) (Fin 1) L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d) :
    PolyhedralPLInCharts d hamiltonMeridianCutAmbientMap (D ×ˢ Icc 0 p) := by
  obtain ⟨_, C, _, _, _, e, he, _⟩ := hamiltonMeridianCut_ballPair
  obtain ⟨f, ⟨K, hK, hKD, _⟩, _⟩ := he
  let a : (V2 × ℝ) →ᴬ[ℝ] ((Fin 2 ⊕ Fin 1) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 2) (Fin 1)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((ContinuousLinearMap.fst ℝ V2 ℝ).prod
          (ContinuousLinearMap.pi fun _ : Fin 1 =>
            ContinuousLinearMap.snd ℝ V2 ℝ)).toContinuousAffineMap
  have ha : FinitePiecewiseAffineOn a (D ×ˢ Icc 0 p) :=
    ⟨K, hK, hKD, K.affineOnFaces_affine a⟩
  exact hd.polyhedralPL_projection ha

end PoincareConjecture.M76
