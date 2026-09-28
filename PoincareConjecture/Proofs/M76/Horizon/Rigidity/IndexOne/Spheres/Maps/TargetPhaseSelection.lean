import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.ScalarTranslation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.TargetTranslation
import PoincareConjecture.Proofs.M76.Rigidity.LocalEmbeddedParameterCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Polyhedra.Mathlib.PolyhedralPLSelection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedPLDiagram
import PoincareConjecture.Proofs.M76.RelativeApproximation.ChartwiseRestriction
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLFixedChart












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "torus" => hamiltonLowerLatticePiEquiv (Fin 2)


noncomputable def targetPhaseRetraction (theta : ℝ) : C(X, X) where
  toFun x := (x.1, (torus).symm ![torus x.2 0, (theta : C)])
  continuous_toFun := by
    apply continuous_fst.prodMk
    apply (torus).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun x : X => torus x.2 0)
      exact (continuous_apply 0).comp ((torus).continuous.comp continuous_snd)
    · exact continuous_const


noncomputable def handlePhaseRetraction (theta : ℝ) : C(H, H) where
  toFun x := (x.1, (torus).symm ![torus x.2 0, (theta : C)])
  continuous_toFun := by
    apply continuous_fst.prodMk
    apply (torus).symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun x : H => torus x.2 0)
      exact (continuous_apply 0).comp ((torus).continuous.comp continuous_snd)
    · exact continuous_const

theorem targetPhaseRetraction_interval (theta : ℝ) (x : X) :
    (targetPhaseRetraction theta x).1 = x.1 := rfl

theorem handlePhaseRetraction_interval (theta : ℝ) (x : H) :
    (handlePhaseRetraction theta x).1 = x.1 := rfl

theorem handlePhaseRetraction_domain (theta : ℝ) (x : H) :
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
      (handlePhaseRetraction theta x) : X) =
      targetPhaseRetraction theta ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) := rfl

theorem targetPhaseRetraction_coordinates (theta : ℝ) (x : X) :
    torus (targetPhaseRetraction theta x).2 = ![torus x.2 0, (theta : C)] :=
  (torus).apply_symm_apply _

theorem handlePhaseRetraction_coordinates (theta : ℝ) (x : H) :
    hamiltonOneHierarchyCoordinates (handlePhaseRetraction theta x) =
      ((hamiltonOneHierarchyCoordinates x).1, (theta : C)) := by
  change ((x.1, torus ((torus).symm ![torus x.2 0, (theta : C)]) 0),
    torus ((torus).symm ![torus x.2 0, (theta : C)]) 1) = _
  rw [(torus).apply_symm_apply]
  rfl

theorem targetPhaseRetraction_mk (theta : ℝ) (x : V1) (v : V2) :
    targetPhaseRetraction theta (x, QuotientAddGroup.mk v) =
      (x, QuotientAddGroup.mk ![v 0, theta]) := by
  apply Prod.ext
  · rfl
  apply (torus).injective
  rw [targetPhaseRetraction_coordinates]
  funext j
  fin_cases j <;> rfl

theorem handlePhaseRetraction_boundary_iff (theta : ℝ) (x : H) :
    handlePhaseRetraction theta x ∈ B ↔ x ∈ B := Iff.rfl

theorem targetPhaseRetraction_domain_iff (theta : ℝ) (x : X) :
    targetPhaseRetraction theta x ∈ R ↔ x ∈ R := Iff.rfl



theorem polyhedralPL_targetPhaseRetraction
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (theta : ℝ) {Y : E → X} {S : Set E}
    (hY : PolyhedralPLInCharts d Y S) :
    PolyhedralPLInCharts d (targetPhaseRetraction theta ∘ Y) S := by
  classical
  let V := (Fin 1 ⊕ Fin 2) → ℝ
  let pi := latticeCoordinateProjection (Fin 1) (Fin 2) L
  let m : V →L[ℝ] V := ContinuousLinearMap.pi fun j =>
    if j = Sum.inr (1 : Fin 2) then 0 else ContinuousLinearMap.proj j
  let b : V := fun j => if j = Sum.inr (1 : Fin 2) then theta else 0
  let a : V →ᴬ[ℝ] V := m.toContinuousAffineMap + ContinuousAffineMap.const ℝ V b
  have hretract (v : V) : targetPhaseRetraction theta (pi v) = pi (a v) := by
    change targetPhaseRetraction theta
      ((fun i => v (Sum.inl i)), QuotientAddGroup.mk (fun j => v (Sum.inr j))) = _
    rw [targetPhaseRetraction_mk]
    apply Prod.ext
    · funext i
      change v (Sum.inl i) = (a v) (Sum.inl i)
      simp [a, b, m, V]
    · apply congrArg QuotientAddGroup.mk
      funext j
      fin_cases j <;> simp [a, b, m, V]
  refine ⟨(targetPhaseRetraction theta).continuous.comp_continuousOn hY.continuousOn, ?_⟩
  intro x
  obtain ⟨i, J, U, hJ, hJS, hU, hxU, hUJ, hYi, hcoords⟩ := hY.coordinates x
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let split := (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin 2)
    (fun _ => ℝ)).toContinuousAffineEquiv
  let lift := a0.trans split.symm
  have hlift (z : V3) (hz : z ∈ (d i).target) : pi (lift z) = (d i).symm z := by
    rw [ha0 z hz]
    rfl
  let v : E → V := lift ∘ (d i) ∘ Y
  have hv : FinitePiecewiseAffineOn v J.space := by
    simpa only [v, Function.comp_def, ContinuousAffineEquiv.coe_toContinuousAffineMap] using
      hcoords.postcomp lift.toContinuousAffineMap
  have hprojection (y : E) (hy : y ∈ J.space) : pi (v y) = Y y := by
    change pi (lift (d i (Y y))) = Y y
    rw [hlift _ ((d i).map_source (hYi hy)), (d i).left_inv (hYi hy)]
  have hlocal : PolyhedralPLInCharts d (targetPhaseRetraction theta ∘ Y) J.space := by
    apply (hd.polyhedralPL_projection (hv.postcomp a)).congr
    intro y hy
    change pi (a (v y)) = targetPhaseRetraction theta (Y y)
    rw [← hretract, hprojection y hy]
  have hxJ : (x : E) ∈ J.space := hUJ ⟨x, hxU, rfl⟩
  obtain ⟨j, N, W, hN, hNJ, hW, hxW, hWN, htarget, hformula⟩ :=
    hlocal.coordinates ⟨x, hxJ⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  have hxO : (x : E) ∈ O := by
    change (⟨x, hxJ⟩ : J.space) ∈ Subtype.val ⁻¹' O
    rw [hOW]
    exact hxW
  refine ⟨j, N, U ∩ (Subtype.val : S → E) ⁻¹' O,
    hN, hNJ.trans hJS, hU.inter (hO.preimage continuous_subtype_val),
    ⟨hxU, hxO⟩, ?_, htarget, hformula⟩
  rintro y ⟨z, hz, rfl⟩
  have hzJ : (z : E) ∈ J.space := hUJ ⟨z, hz.1, rfl⟩
  have hzW : (⟨z, hzJ⟩ : J.space) ∈ W := by
    rw [← hOW]
    exact hz.2
  exact hWN ⟨⟨z, hzJ⟩, hzW, rfl⟩

theorem targetPhaseRetraction_eq_of_coe_eq {a b : ℝ} (hab : (a : C) = (b : C)) :
    targetPhaseRetraction a = targetPhaseRetraction b := by
  apply ContinuousMap.ext
  intro x
  change (x.1, (torus).symm ![torus x.2 0, (a : C)]) =
    (x.1, (torus).symm ![torus x.2 0, (b : C)])
  rw [hab]

theorem targetPhaseRetraction_phase (theta : ℝ) (x : X) :
    torus (targetPhaseRetraction theta x).2 1 = (theta : C) := by
  rw [targetPhaseRetraction_coordinates]
  rfl

theorem targetPhaseRetraction_fixed (theta : ℝ) (x : X)
    (hx : torus x.2 1 = (theta : C)) : targetPhaseRetraction theta x = x := by
  apply Prod.ext
  · rfl
  apply (torus).injective
  rw [targetPhaseRetraction_coordinates, ← hx]
  funext i
  fin_cases i <;> rfl

private theorem selection_coordinates_of_missing_branch
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f₀ f₁ f₂ g : E → X}
    (h₀ : PolyhedralPLInCharts d f₀ K.space) (h₁ : PolyhedralPLInCharts d f₁ K.space)
    (h₂ : ContinuousOn f₂ K.space) (hg : ContinuousOn g K.space)
    (hselect : ∀ y ∈ K.space, g y = f₀ y ∨ g y = f₁ y ∨ g y = f₂ y)
    (x : K.space) (hx : g x ≠ f₂ x) :
    ∃ (i : β) (J : SimplicialComplex ℝ E) (W : Set K.space),
      J.faces.Finite ∧ J.space ⊆ K.space ∧ IsOpen W ∧ x ∈ W ∧
      Subtype.val '' W ⊆ J.space ∧ MapsTo g J.space (d i).source ∧
      FinitePiecewiseAffineOn ((d i) ∘ g) J.space := by
  let : T2Space X := ((Homeomorph.refl V1).prodCongr (torus)).isEmbedding.t2Space
  let U : Set K.space := {z | g z ≠ f₂ z}
  have hU : IsOpen U := (isClosed_eq hg.domRestrict h₂.domRestrict).isOpen_compl
  obtain ⟨N, V, hN, hNK, hV, hxV, hVN, hNU⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hU hx
  have hlocal : PolyhedralPLInCharts d g N.space :=
    (h₀.restrict_finite N hN hNK).continuous_selection hd.domain.cover hd.domain.compatible
      N hN (h₁.restrict_finite N hN hNK) (hg.mono hNK) (by
        intro y hy
        rcases hselect y (hNK hy) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact ((hNU (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)) h).elim)
  have hxN : (x : E) ∈ N.space := hVN ⟨x, hxV, rfl⟩
  obtain ⟨i, J, W, hJ, hJN, hW, hxW, hWJ, htarget, hformula⟩ := hlocal.coordinates ⟨x, hxN⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.mp hW
  have hxO : (x : E) ∈ O := by
    change (⟨x, hxN⟩ : N.space) ∈ Subtype.val ⁻¹' O
    rw [hOW]
    exact hxW
  refine ⟨i, J, V ∩ (Subtype.val : K.space → E) ⁻¹' O,
    hJ, hJN.trans hNK, hV.inter (hO.preimage continuous_subtype_val),
    ⟨hxV, hxO⟩, ?_, htarget, hformula⟩
  rintro y ⟨z, hz, rfl⟩
  have hzN : (z : E) ∈ N.space := hVN ⟨z, hz.1, rfl⟩
  have hzW : (⟨z, hzN⟩ : N.space) ∈ W := by
    rw [← hOW]
    exact hz.2
  exact hWJ ⟨⟨z, hzN⟩, hzW, rfl⟩



theorem polyhedralPL_targetPhaseSelection
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (a b : ℝ) (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {Y g : E → X} (hY : PolyhedralPLInCharts d Y K.space) (hg : ContinuousOn g K.space)
    (hselect : ∀ x ∈ K.space, g x = Y x ∨
      g x = targetPhaseRetraction a (Y x) ∨ g x = targetPhaseRetraction b (Y x)) :
    PolyhedralPLInCharts d g K.space := by
  let : T2Space X := ((Homeomorph.refl V1).prodCongr (torus)).isEmbedding.t2Space
  have ha := polyhedralPL_targetPhaseRetraction hd a hY
  have hb := polyhedralPL_targetPhaseRetraction hd b hY
  by_cases hab : (a : C) = (b : C)
  · apply hY.continuous_selection hd.domain.cover hd.domain.compatible K hK ha hg
    intro x hx
    rcases hselect x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr (by rw [targetPhaseRetraction_eq_of_coe_eq hab]; exact h)
  · refine ⟨hg, ?_⟩
    intro x
    by_cases hx : g x = targetPhaseRetraction b (Y x)
    · have hx' : g x ≠ targetPhaseRetraction a (Y x) := by
        intro he
        have hh := congrArg (fun z : X => torus z.2 1) (he.symm.trans hx)
        exact hab (by simpa only [targetPhaseRetraction_phase] using hh)
      exact selection_coordinates_of_missing_branch hd K hK hY hb ha.continuousOn hg
        (fun y hy => by
          rcases hselect y hy with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)) x hx'
    · exact selection_coordinates_of_missing_branch hd K hK hY ha hb.continuousOn hg hselect x hx



theorem chartwisePL_of_targetPhaseSelection
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (a b : ℝ) (psi : C(H, H))
    (hselect : ∀ x : H, psi x = phi x ∨
      psi x = handlePhaseRetraction a (phi x) ∨
      psi x = handlePhaseRetraction b (phi x)) :
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) := by
  have hempty : ChartwisePLOn e d
      (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∅ :=
    hphi.congr_mono isOpen_empty (empty_subset _) (fun _ hx => hx.elim)
  apply chartwisePLMap_of_open_and_embedded_parameters (E := V3) e d _ hempty
  intro x _
  obtain ⟨K, q, z, hK, hq, hiq, hqz, hrange, hqPL⟩ :=
    exists_relative_source_parameter e d _ hphi x
  have hY := hphi.polyhedralPLInCharts_comp K hK q hq hqPL (fun _ _ => mem_univ _)
  refine ⟨K, q, z, hK, hq, hiq, hqz, hrange, hqPL, ?_⟩
  apply polyhedralPL_targetPhaseSelection hd a b K hK hY
  · exact (continuous_subtype_val.comp
      (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi).continuous).comp_continuousOn hq
  · intro u _
    rcases hselect (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (q u)) with h | h | h
    · exact Or.inl (congrArg (fun y : H =>
        ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm y : X)) h)
    · exact Or.inr (Or.inl (congrArg (fun y : H =>
        ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm y : X)) h))
    · exact Or.inr (Or.inr (congrArg (fun y : H =>
        ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm y : X)) h))



theorem chartwisePL_handlePhaseRetraction_comp
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (theta : ℝ) :
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L
      ((handlePhaseRetraction theta).comp phi)) :=
  chartwisePL_of_targetPhaseSelection hd hphi theta theta _
    (fun _ => Or.inr (Or.inl rfl))

theorem targetPhaseSelection_interval {phi psi : C(H, H)} {a b : ℝ}
    (hselect : ∀ x : H, psi x = phi x ∨
      psi x = handlePhaseRetraction a (phi x) ∨
      psi x = handlePhaseRetraction b (phi x)) (x : H) :
    (psi x).1 = (phi x).1 := by
  rcases hselect x with h | h | h <;> rw [h] <;> rfl

theorem targetPhaseSelection_boundary_iff {phi psi : C(H, H)} {a b : ℝ}
    (hselect : ∀ x : H, psi x = phi x ∨
      psi x = handlePhaseRetraction a (phi x) ∨
      psi x = handlePhaseRetraction b (phi x)) (x : H) :
    psi x ∈ B ↔ phi x ∈ B := by
  rcases hselect x with h | h | h <;> rw [h] <;> rfl

end PoincareConjecture.M76.HamiltonIntervalTorus
