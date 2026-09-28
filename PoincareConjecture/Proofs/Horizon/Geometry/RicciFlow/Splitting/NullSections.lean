import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciNullity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.KernelTransport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Coordinates
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow.Splitting

open Poincare.RicciFlow.Splitting LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma inverse_regularized_mem_kernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) (K : Submodule ℝ E)
    (hB : (A + K.starProjection).IsInvertible)
    (hdim : Module.finrank ℝ A.ker = Module.finrank ℝ K) (c : K) :
    A ((A + K.starProjection).inverse c) = 0 := by
  let L : A.ker →ₗ[ℝ] K :=
    K.orthogonalProjectionOnto.toLinearMap.comp A.ker.subtype
  have hL : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    apply hB.injective
    change A x + K.starProjection x = A y + K.starProjection y
    rw [show A x = 0 from x.property, show A y = 0 from y.property, zero_add, zero_add]
    exact congrArg Subtype.val hxy
  obtain ⟨z, hz⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hL c
  have hsolve : (A + K.starProjection) z = c := by
    change A z + K.starProjection z = c
    rw [show A z = 0 from z.property, zero_add]
    exact congrArg Subtype.val hz
  rw [hB.inverse_apply_eq.mpr hsolve.symm]
  exact z.property

omit [IsManifold (𝓡 n) ∞ M] in

theorem exists_local_contMDiff_kernel_section
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {A : M → E →L[ℝ] E} {U : Set M} (hU : IsOpen U)
    (hA : ContMDiffOn (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ A U) {p : M} (hp : p ∈ U)
    (hsym : (A p).toLinearMap.IsSymmetric)
    (hdim : ∀ q ∈ U, Module.finrank ℝ (A q).ker = Module.finrank ℝ (A p).ker)
    (v : E) (hv : A p v = 0) :
    ∃ (V : Set M) (s : M → E), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ s V ∧ s p = v ∧ ∀ q ∈ V, A q (s q) = 0 := by
  let K := (A p).ker
  let B := fun q => A q + K.starProjection
  have hBp : (B p).IsInvertible := isInvertible_add_kernel_projection (A p) hsym
  have hnear : ∀ᶠ q in 𝓝 p, IsUnit (B q) :=
    ((hA.continuousOn.continuousAt (hU.mem_nhds hp)).add_const K.starProjection).eventually
      (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr hBp.bijective))
  obtain ⟨V, hVB, hVo, hpV⟩ := mem_nhds_iff.mp hnear
  let W := V ∩ U
  have hB (q : M) (hq : q ∈ W) : (B q).IsInvertible := by
    rcases hVB hq.1 with ⟨e, he⟩
    exact ⟨ContinuousLinearEquiv.ofUnit e, he⟩
  refine ⟨W, fun q => (B q).inverse v, hVo.inter hU, ⟨hpV, hp⟩,
    inter_subset_right, ?_, ?_, ?_⟩
  · intro q hq
    have hBq : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ B q :=
      ((hA q hq.2).contMDiffAt (hU.mem_nhds hq.2)).add contMDiffAt_const
    exact (((hB q hq).contDiffAt_map_inverse.contMDiffAt.comp q hBq).clm_apply
      contMDiffAt_const).contMDiffWithinAt
  · apply hBp.inverse_apply_eq.mpr
    change v = A p v + K.starProjection v
    rw [hv, zero_add, K.starProjection_mem_subspace_eq_self ⟨v, hv⟩]
  · intro q hq
    exact inverse_regularized_mem_kernel (A q) K (hB q hq) (hdim q hq.2) ⟨v, hv⟩

def coordinateRicciBilinear (D : LeviCivitaData g) (p x : M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  let B := (ricciBilinear D x).compl₁₂ (e.symmL ℝ x).toLinearMap
    (e.symmL ℝ x).toLinearMap
  (LinearMap.toContinuousLinearMap.toLinearMap.comp B).toContinuousLinearMap

lemma coordinateRicciBilinear_apply (D : LeviCivitaData g) (p x : M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    coordinateRicciBilinear D p x v w =
      D.ricci x (constantCoordinateField p v x) (constantCoordinateField p w x) := by
  change ricciBilinear D x _ _ = _
  exact ricciBilinear_apply _ _ _ _

def coordinateRicciOperator (D : LeviCivitaData g) (p x : M) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  InnerProductSpace.continuousLinearMapOfBilin (coordinateRicciBilinear D p x)

lemma coordinateRicciOperator_inner (D : LeviCivitaData g) (p x : M)
    (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (coordinateRicciOperator D p x v) w =
      D.ricci x (constantCoordinateField p v x) (constantCoordinateField p w x) := by
  rw [coordinateRicciOperator, InnerProductSpace.continuousLinearMapOfBilin_apply,
    coordinateRicciBilinear_apply]

private lemma contMDiffAt_coordinateRicciOperator (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (p : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) ∞ (coordinateRicciOperator D p) x := by
  have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞ (coordinateRicciBilinear D p) x := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply contMDiffAt_clm_of_apply
    intro w
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
    have h := hD.2.1.2 e.baseSet e.open_baseSet
      ![constantCoordinateField p v, constantCoordinateField p w]
      (by intro i; fin_cases i <;> exact fun y hy =>
        (contMDiffAt_constantCoordinateField p _ hy).contMDiffWithinAt)
    simpa only [coordinateRicciBilinear_apply, ricciEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one] using
      (h x hx).contMDiffAt (e.open_baseSet.mem_nhds hx)
  exact contMDiffAt_const.clm_comp hB

lemma coordinateRicciOperator_eq_zero_iff (D : LeviCivitaData g)
    (p : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet) (v : EuclideanSpace ℝ (Fin n)) :
    coordinateRicciOperator D p x v = 0 ↔
      ∀ w, D.ricci x (constantCoordinateField p v x) w = 0 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  constructor
  · intro hv w
    have h := coordinateRicciOperator_inner D p x v (e.continuousLinearMapAt ℝ x w)
    rw [hv, inner_zero_left] at h
    change 0 = D.ricci x (constantCoordinateField p v x)
      (e.symmL ℝ x (e.continuousLinearMapAt ℝ x w)) at h
    rw [e.symmL_continuousLinearMapAt hx] at h
    exact h.symm
  · intro hv
    apply ext_inner_right ℝ
    intro w
    rw [coordinateRicciOperator_inner, hv, inner_zero_left]

lemma coordinateRicciOperator_finrank_ker (D : LeviCivitaData g)
    (p : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p).baseSet) :
    Module.finrank ℝ (coordinateRicciOperator D p x).ker = ricciNullity D x := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  let L := e.continuousLinearEquivAt ℝ x hx
  have hker : (coordinateRicciOperator D p x).ker =
      (ricciKernel D x).map L.toLinearEquiv.toLinearMap := by
    ext v
    rw [Submodule.mem_map_equiv, mem_ricciKernel]
    change coordinateRicciOperator D p x v = 0 ↔ _
    rw [coordinateRicciOperator_eq_zero_iff D p hx]
    change (∀ w, D.ricci x (constantCoordinateField p v x) w = 0) ↔
      ∀ w, D.ricci x (L.symm v) w = 0
    rw [show L.symm v = constantCoordinateField p v x from
      congrFun (e.symm_continuousLinearEquivAt_eq hx) v]
  rw [hker, LinearEquiv.finrank_map_eq]
  rfl

theorem exists_local_smooth_ricci_null_section (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) {x : M}
    (hdim : ∀ᶠ y in 𝓝 x, ricciNullity D y = ricciNullity D x)
    (v : TangentSpace (𝓡 n) x) (hv : ∀ w, D.ricci x v w = 0) :
    ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧ V x = v ∧
      ∀ y ∈ U, ∀ w, D.ricci y (V y) w = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace (𝓡 n)) x
  obtain ⟨W, hWdim, hWo, hxW⟩ := mem_nhds_iff.mp hdim
  let U := W ∩ e.baseSet
  have hU : IsOpen U := hWo.inter e.open_baseSet
  have hxU : x ∈ U := ⟨hxW, hx⟩
  let A := coordinateRicciOperator D x
  have hA : ContMDiffOn (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ A U := fun y hy =>
    (contMDiffAt_coordinateRicciOperator D hD x hy.2).contMDiffWithinAt
  have hsym : (A x).toLinearMap.IsSymmetric := by
    intro u w
    change inner ℝ (A x u) w = inner ℝ u (A x w)
    conv_rhs => rw [real_inner_comm]
    rw [coordinateRicciOperator_inner, coordinateRicciOperator_inner]
    exact (hD.2.2.2.1 x _ _ 0 0).2.2.2
  have hAdim (y : M) (hy : y ∈ U) :
      Module.finrank ℝ (A y).ker = Module.finrank ℝ (A x).ker := by
    rw [coordinateRicciOperator_finrank_ker D x hy.2,
      coordinateRicciOperator_finrank_ker D x hx]
    exact hWdim hy.1
  let v₀ := e.continuousLinearMapAt ℝ x v
  have hv₀ : A x v₀ = 0 := by
    apply (coordinateRicciOperator_eq_zero_iff D x hx v₀).mpr
    change ∀ w, D.ricci x (e.symmL ℝ x (e.continuousLinearMapAt ℝ x v)) w = 0
    rw [e.symmL_continuousLinearMapAt hx]
    exact hv
  obtain ⟨O, s, hOo, hxO, hOU, hs, hsx, hsnull⟩ :=
    exists_local_contMDiff_kernel_section hU hA hxU hsym hAdim v₀ hv₀
  let V : (y : M) → TangentSpace (𝓡 n) y := fun y => e.symmL ℝ y (s y)
  refine ⟨O, V, hOo, hxO, ?_, ?_, ?_⟩
  · intro y hy
    have hs' : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (fun z : M => TotalSpace.mk' E z (s z)) y := by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, (hs y hy).contMDiffAt (hOo.mem_nhds hy)⟩
    exact ((e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞) (hOU hy).2).clm_bundle_apply
      hs').contMDiffWithinAt
  · change e.symmL ℝ x (s x) = v
    rw [hsx]
    exact e.symmL_continuousLinearMapAt hx v
  · intro y hy
    exact (coordinateRicciOperator_eq_zero_iff D x (hOU hy).2 (s y)).mp (hsnull y hy)

end PoincareConjecture.RicciFlow.Splitting
