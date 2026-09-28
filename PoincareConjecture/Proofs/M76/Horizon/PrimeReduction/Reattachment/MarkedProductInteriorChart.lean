import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBallInteriorChart
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "ClosedCube" => Set.prod (Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1)
local notation "OpenCube" => Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1)

noncomputable def markedProductCoordinates : V3 ≃ᴬ[ℝ] P3 :=
  (LinearEquiv.toContinuousLinearEquiv
    ({ toFun := fun x => ((x 0,x 1),x 2)
       invFun := fun x => ![x.1.1,x.1.2,x.2]
       left_inv := by intro x; funext i; fin_cases i <;> rfl
       right_inv := by intro x; rfl
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } : V3 ≃ₗ[ℝ] P3)).toContinuousAffineEquiv

theorem markedProductCoordinates_apply (x : V3) :
    markedProductCoordinates x = ((x 0,x 1),x 2) := rfl

theorem markedProductCoordinates_preimage_closedCube :
    markedProductCoordinates ⁻¹' ClosedCube = closedBall (0 : V3) 1 := by
  ext x
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  change ((-1 ≤ x 0 ∧ x 0 ≤ 1) ∧ (-1 ≤ x 1 ∧ x 1 ≤ 1)) ∧
    (-1 ≤ x 2 ∧ x 2 ≤ 1) ↔ ∀ i, ‖x i‖ ≤ 1
  simp only [Real.norm_eq_abs,abs_le]
  constructor
  · rintro ⟨⟨h0,h1⟩,h2⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨h 0,h 1⟩,h 2⟩

theorem markedProductCoordinates_preimage_openCube :
    markedProductCoordinates ⁻¹' OpenCube = ball (0 : V3) 1 := by
  have hint : interior ClosedCube = OpenCube := by
    change interior ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (-1 : ℝ) 1) = _
    simp only [interior_prod_eq,interior_Icc]
    rfl
  rw [← hint]
  change markedProductCoordinates.toHomeomorph ⁻¹' interior ClosedCube = _
  rw [markedProductCoordinates.toHomeomorph.preimage_interior]
  change interior (markedProductCoordinates ⁻¹' ClosedCube) = _
  rw [markedProductCoordinates_preimage_closedCube,interior_closedBall _ one_ne_zero]

theorem exists_marked_product_interior_chart
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {D : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (p : P3 → X) (hp : PolyhedralPLInCharts e p ClosedCube)
    (hpi : InjOn p ClosedCube) (himage : p '' ClosedCube = D)
    (hboundary : ∀ z ∈ ClosedCube, p z ∈ frontier D ↔ z ∈ frontier ClosedCube) :
    ∃ Q : OpenPartialHomeomorph X V3,
      Q.source = interior D ∧ Q.target = markedProductCoordinates ⁻¹' OpenCube ∧
      (∀ y, Q.symm y = p (markedProductCoordinates y)) ∧
      ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
  classical
  let a := markedProductCoordinates
  have ha : MapsTo a (closedBall (0 : V3) 1) ClosedCube :=
    markedProductCoordinates_preimage_closedCube.symm.subset
  have hai : InjOn (p ∘ a) (closedBall (0 : V3) 1) := hpi.comp a.injective.injOn ha
  have haimage : a '' closedBall (0 : V3) 1 = ClosedCube := by
    rw [← markedProductCoordinates_preimage_closedCube]
    exact a.surjective.image_preimage _
  have hpimage : (p ∘ a) '' closedBall (0 : V3) 1 = D := by
    rw [image_comp,haimage,himage]
  have hPL : PolyhedralPLInCharts e (p ∘ a) (closedBall (0 : V3) 1) := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
      isFinitePLBallPair_unit_cube (ι := Fin 3)
    rw [← hKs]
    exact hp.comp_finitePiecewiseAffineOn K hK
      ⟨K,hK,rfl,K.affineOnFaces_affine a.toContinuousAffineMap⟩
      (fun x hx => ha (hKs.subset hx))
  let C : closedBall (0 : V3) 1 ≃ₜ D :=
    (Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn (p ∘ a) _ hai)
      (hPL.continuousOn.domRestrict.subtype_mk _)).trans (Homeomorph.setCongr hpimage)
  have hDclosed : IsClosed D := by
    rw [← himage]
    exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).image_of_continuousOn
      hp.continuousOn).isClosed
  have hfront : a ⁻¹' frontier ClosedCube = sphere (0 : V3) 1 := by
    change a.toHomeomorph ⁻¹' frontier ClosedCube = _
    rw [a.toHomeomorph.preimage_frontier]
    change frontier (markedProductCoordinates ⁻¹' ClosedCube) = _
    rw [markedProductCoordinates_preimage_closedCube,frontier_closedBall _ one_ne_zero]
  let b : ChartwisePLBall e D (frontier D) := {
    boundary_subset := hDclosed.frontier_subset
    parametrization := C
    map := p ∘ a
    map_eq := fun _ => rfl
    piecewiseAffine := hPL
    boundary_eq := fun x => (hboundary (a x) (ha x.property)).trans
      (show a x ∈ frontier ClosedCube ↔ (x : V3) ∈ sphere (0 : V3) 1 from
        Set.ext_iff.mp hfront x) }
  obtain ⟨Q,hQs,hQt,hQinv,_,hQcompat⟩ := b.exists_original_interior_chart he
  exact ⟨Q,hQs,hQt.trans markedProductCoordinates_preimage_openCube.symm,hQinv,hQcompat⟩

end PoincareConjecture.M76
