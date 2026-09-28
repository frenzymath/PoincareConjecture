import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)

noncomputable def stackCapEndChart
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (R : E2 ≃ₗᵢ[ℝ] E2) :
    OpenPartialHomeomorph P P :=
  let A := (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans
    (R.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  let H := (heightPlaneCoordinates u).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ)
  (A.toHomeomorph.transOpenPartialHomeomorph C.tube).transHomeomorph H.toHomeomorph

theorem stackCapEndChart_spec
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (R : E2 ≃ₗᵢ[ℝ] E2) :
    let T := stackCapEndChart C R
    T.source = {p : P | (R p.2, p.1) ∈ C.tube.source} ∧
    T.target = {p : P |
      (heightPlaneCoordinates u).symm (p.2,p.1) ∈ C.tube.target} ∧
    (∀ p : P, T p =
      ((heightPlaneCoordinates u (C.tube (R p.2,p.1))).2,
       (heightPlaneCoordinates u (C.tube (R p.2,p.1))).1)) ∧
    (∀ p : P, T.symm p =
      ((C.tube.symm ((heightPlaneCoordinates u).symm (p.2,p.1))).2,
       R.symm (C.tube.symm
         ((heightPlaneCoordinates u).symm (p.2,p.1))).1)) ∧
    ContDiffOn ℝ ∞ T T.source ∧
    ContDiffOn ℝ ∞ T.symm T.target ∧
    (univ : Set ℝ) ×ˢ closedBall (0 : E2) 1 ⊆ T.source ∧
    (∀ p ∈ T.source, (T p).1 = p.1) ∧
    (∀ p ∈ T.target, (T.symm p).1 = p.1) := by
  let A := (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans
    (R.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  let H := (heightPlaneCoordinates u).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ)
  let T := stackCapEndChart C R
  have hh (p : P) (hp : p ∈ T.source) : (T p).1 = p.1 := by
    change (heightPlaneCoordinates u (C.tube (R p.2, p.1))).2 = p.1
    rw [heightPlaneCoordinates_snd]
    exact C.tube_height _ hp
  refine ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, hh, ?_⟩
  · exact H.contDiff.comp_contDiffOn
      (C.tube_smooth.comp A.contDiff.contDiffOn (fun _ hp => hp))
  · exact A.symm.contDiff.comp_contDiffOn
      (C.tube_inverse.comp H.symm.contDiff.contDiffOn (fun _ hp => hp))
  · intro p hp
    change (R p.2, p.1) ∈ C.tube.source
    exact C.tube_source ⟨mem_closedBall_zero_iff.mpr (by
      rw [R.norm_map]
      exact mem_closedBall_zero_iff.mp hp.2), mem_univ _⟩
  · intro p hp
    have h := hh (T.symm p) (T.map_target hp)
    rw [T.right_inv hp] at h
    exact h.symm

noncomputable def stackCapEndFiber
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (R : E2 ≃ₗᵢ[ℝ] E2) (z : ℝ) :
    BallNeighborhoodChart E2 E2 := by
  let T := stackCapEndChart C R
  have h := stackCapEndChart_spec C R
  have hT := h.2.2.2.2.1
  have hTi := h.2.2.2.2.2.1
  have hsrc := h.2.2.2.2.2.2.1
  have hh := h.2.2.2.2.2.2.2.1
  have hhi := h.2.2.2.2.2.2.2.2
  have hf : ContDiffOn ℝ ∞ (fun x : E2 => (T (z, x)).2)
      {x | (z, x) ∈ T.source} :=
    (hT.comp (contDiff_prodMk_right z).contDiffOn (fun _ hx => hx)).snd
  have hi : ContDiffOn ℝ ∞ (fun y : E2 => (T.symm (z, y)).2)
      {y | (z, y) ∈ T.target} :=
    (hTi.comp (contDiff_prodMk_right z).contDiffOn (fun _ hy => hy)).snd
  have hforward (x : E2) (hx : (z, x) ∈ T.source) :
      (z, (T (z, x)).2) = T (z, x) := Prod.ext (hh (z, x) hx).symm rfl
  have hinverse (y : E2) (hy : (z, y) ∈ T.target) :
      (z, (T.symm (z, y)).2) = T.symm (z, y) :=
    Prod.ext (hhi (z, y) hy).symm rfl
  let e : OpenPartialHomeomorph E2 E2 := {
    toFun := fun x => (T (z, x)).2
    invFun := fun y => (T.symm (z, y)).2
    source := {x | (z, x) ∈ T.source}
    target := {y | (z, y) ∈ T.target}
    map_source' := by
      intro x hx
      change (z, (T (z, x)).2) ∈ T.target
      rw [hforward x hx]
      exact T.map_source hx
    map_target' := by
      intro y hy
      have h := T.map_target hy
      change (z, (T.symm (z, y)).2) ∈ T.source
      rw [hinverse y hy]
      exact h
    left_inv' := by
      intro x hx
      rw [hforward x hx, T.left_inv hx]
    right_inv' := by
      intro y hy
      rw [hinverse y hy, T.right_inv hy]
    open_source := T.open_source.preimage (continuous_const.prodMk continuous_id)
    open_target := T.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hi.continuousOn }
  exact ⟨e, fun _ hx => hsrc ⟨mem_univ _, hx⟩, hf, hi⟩

theorem stackCapEndFiber_spec
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (R : E2 ≃ₗᵢ[ℝ] E2) :
    let T := stackCapEndChart C R
    (∀ z : ℝ,
      let N := stackCapEndFiber C R z
      N.chart.source = {x : E2 | (z,x) ∈ T.source} ∧
      N.chart.target = {y : E2 | (z,y) ∈ T.target} ∧
      (∀ x : E2, N.chart x = (T (z,x)).2) ∧
      (∀ y : E2, N.chart.symm y = (T.symm (z,y)).2) ∧
      (∀ q ∈ sphere (0 : E2) 1,
        (fun x => N.chart x) =ᶠ[𝓝 q] (fun x => (T (z,x)).2))) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => (T (p.1,(p.2 : E2))).2) ∧
    (∀ z : ℝ, IsPlanarEmbedding
      (fun q : UnitCircle => (T (z,(q : E2))).2)) := by
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let T := stackCapEndChart C R
  obtain ⟨_, _, _, _, hT, _, hsrc, _, _⟩ := stackCapEndChart_spec C R
  have hj : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => (T (p.1, (p.2 : E2))).2) := by
    intro p
    have hp : (p.1, (p.2 : E2)) ∈ T.source :=
      hsrc ⟨mem_univ _, sphere_subset_closedBall p.2.property⟩
    have hs : ContDiffAt ℝ ∞ (fun x : P => (T x).2) (p.1, (p.2 : E2)) :=
      (hT.contDiffAt (T.open_source.mem_nhds hp)).snd
    exact ContMDiffAt.comp (I' := 𝓘(ℝ, P))
      (g := fun x : P => (T x).2)
      (f := fun x : ℝ × UnitCircle => (x.1, (x.2 : E2))) p hs.contMDiffAt
      (contMDiffAt_fst.prodMk_space
        ((contMDiff_coe_sphere (E := E2) (n := 1) (m := ∞)).contMDiffAt.comp p
          contMDiffAt_snd))
  refine ⟨?_, hj, ?_⟩
  · intro z
    have he (x : E2) : (stackCapEndFiber C R z).chart x = (T (z, x)).2 := rfl
    exact ⟨rfl, rfl, he, fun _ => rfl,
      fun _ _ => Filter.Eventually.of_forall he⟩
  · intro z
    let N := stackCapEndFiber C R z
    have he : (N.chart : E2 → E2) = fun x => (T (z, x)).2 := rfl
    clear_value N
    have hsm : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞
        (fun q : UnitCircle => (T (z, (q : E2))).2) := by
      have hp : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
          (fun q : UnitCircle => (z, q)) := contMDiff_const.prodMk contMDiff_id
      exact ContMDiff.comp (I' := 𝓘(ℝ, ℝ).prod (𝓡 1))
        (g := fun p : ℝ × UnitCircle => (T (p.1, (p.2 : E2))).2)
        (f := fun q : UnitCircle => (z, q)) hj hp
    refine ⟨hsm, ?_, ?_⟩
    · intro p q hpq
      apply Subtype.ext
      apply N.chart.injOn
        (N.closedBall_subset_source (sphere_subset_closedBall p.property))
        (N.closedBall_subset_source (sphere_subset_closedBall q.property))
      rw [he]
      exact hpq
    · intro q
      let i : UnitCircle → E2 := fun p => (p : E2)
      have hi : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ i := contMDiff_coe_sphere
      have hdi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) i q) := by
        intro v w hvw
        exact injective_mvfderiv_subtypeVal_sphere q
          (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (q : E2)) hvw)
      have hq := N.closedBall_subset_source (sphere_subset_closedBall q.property)
      obtain ⟨A, hA⟩ := exists_smoothChart_derivative N.chart N.smooth N.smooth_symm hq
      have hcomp : (fun q : UnitCircle => (T (z, (q : E2))).2) = N.chart ∘ i := by
        funext p
        exact (congrFun he (p : E2)).symm
      rw [hcomp]
      rw [mfderiv_comp q hA.differentiableAt.mdifferentiableAt
        (hi.mdifferentiable (by simp) q), mfderiv_eq_fderiv, hA.fderiv]
      exact A.injective.comp hdi

end PoincareConjecture.M25.Topology3D
