import PoincareConjecture.Proofs.M76.Wall.Mathlib.AffineUnionCorner
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.LocalPLScalarArithmetic
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningPatchClosure









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)



theorem exists_union_corner_map_preserving_third_coordinate :
    ∃ H : C3 ≃ₜ C3, H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid C3 ∧
      H 0 = 0 ∧ (∀ z,(H z).2 = z.2) ∧
      (∀ z,(H z).1.1 = max z.1.1 (-z.1.2)) ∧
      (∀ z,(H z).1.2 = z.1.2+z.1.1) ∧
      ∀ z,(H z).1.1 = 0 ↔
        (z.1.1 = 0 ∧ 0 ≤ z.1.2) ∨ (z.1.2 = 0 ∧ z.1.1 ≤ 0) := by
  let a := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let b := -(ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  obtain ⟨h,hh,ha,hb,hfix,_,hzero⟩ := a.exists_union_corner_straightening b
    ((1,0) : P2) ((0,-1) : P2) (by norm_num [a]) (by norm_num [b])
      (by norm_num [a]) (by norm_num [b])
  let H := h.prodCongr (Homeomorph.refl ℝ)
  have hPL (f : P2 → P2) (hf : LocallyPiecewiseAffineOn f univ) :
      LocallyPiecewiseAffineOn (fun z : C3 => (f z.1,z.2)) univ := by
    have hfst := locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap isOpen_univ
    have hsnd := locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap isOpen_univ
    have hcomp : LocallyPiecewiseAffineOn (fun z : C3 => f z.1) univ := by
      simpa [Function.comp_def] using hf.comp hfst
    exact hcomp.prod_mk hsnd
  refine ⟨H,⟨hPL h hh.1,hPL h.symm hh.2⟩,?_,fun _ => rfl,fun z => ha z.1,?_,?_⟩
  · exact Prod.ext (hfix 0 rfl (by simp [b])) rfl
  · intro z
    have ht := hb z.1
    change -(h z.1).2 = -z.1.2-z.1.1 at ht
    change (h z.1).2 = z.1.2+z.1.1
    linarith
  · intro z
    simpa [a,b,H] using hzero z.1



theorem exists_original_corner_pair_chart
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i,(e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : V3 ≃L[ℝ] C3) {S F : Set X} {x : X}
    (hx : x ∈ Q.source) (hQx : Q x = 0)
    (hS : ∀ y ∈ Q.source,y ∈ S ↔
      ((A (Q y)).1.1 = 0 ∧ 0 ≤ (A (Q y)).1.2) ∨
      ((A (Q y)).1.2 = 0 ∧ (A (Q y)).1.1 ≤ 0))
    (hF : ∀ y ∈ Q.source,y ∈ F ↔ (A (Q y)).2 = 0) :
    ∃ P : OpenPartialHomeomorph X V3,
      P.source = Q.source ∧ x ∈ P.source ∧ P x = 0 ∧
      (∀ i,(e i).symm.trans P ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ P.source,(A (P y)).2 = (A (Q y)).2) ∧
      (∀ y ∈ P.source,y ∈ S ↔ (A (P y)).1.1 = 0) ∧
      ∀ y ∈ P.source,y ∈ F ↔ (A (P y)).2 = 0 := by
  obtain ⟨H,hH,hH0,hthird,_,_,hcorner⟩ := exists_union_corner_map_preserving_third_coordinate
  let N := A.toHomeomorph.trans (H.trans A.symm.toHomeomorph)
  have hA := locallyPiecewiseAffineOn_affine A.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ
  have hAi := locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ
  have hN : N.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 := by
    have hHf : LocallyPiecewiseAffineOn H univ := hH.1
    have hHi : LocallyPiecewiseAffineOn H.symm univ := hH.2
    constructor
    · change LocallyPiecewiseAffineOn (fun z => A.symm (H (A z))) univ
      simpa [Function.comp_def] using hAi.comp (hHf.comp hA)
    · change LocallyPiecewiseAffineOn (fun z => A.symm (H.symm (A z))) univ
      simpa [Function.comp_def] using hAi.comp (hHi.comp hA)
  let P := Q.trans N.toOpenPartialHomeomorph
  have hPs : P.source = Q.source := by
    change Q.source ∩ Q ⁻¹' univ = Q.source
    rw [preimage_univ,inter_univ]
  have hcoord (y : X) : A (P y) = H (A (Q y)) := A.apply_symm_apply _
  refine ⟨P,hPs,hPs.symm.subset hx,?_,?_,?_,?_,?_⟩
  · change A.symm (H (A (Q x))) = 0
    rw [hQx,map_zero,hH0,map_zero]
  · intro i
    simpa only [P,←OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans (hQ i) hN
  · intro y _
    rw [hcoord,hthird]
  · intro y hy
    rw [hcoord,hcorner]
    exact hS y (hPs.subset hy)
  · intro y hy
    rw [hcoord,hthird]
    exact hF y (hPs.subset hy)



theorem ChartwisePLSphere.exists_original_ball_patch_corner_pair_chart
    {X V ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ι → OpenPartialHomeomorph X V3} {S Q T F : Set X}
    (s : ChartwisePLSphere e S) (u : ChartwisePLBall e Q T)
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d q : Set V} (hd : IsFinitePLBallPair P2 d q)
    (p : V → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcontact : Q ∩ S = p '' d) (hdT : p '' d ⊆ T)
    (hSout : (S \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty)
    (H : OpenPartialHomeomorph X V3)
    (hH : ∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3)
    (A : V3 ≃L[ℝ] C3) {x : X} (hx : x ∈ H.source) (hHx : H x = 0)
    (hS : ∀ y ∈ H.source,y ∈ S ↔ (A (H y)).1.1 = 0)
    (hQ : ∀ y ∈ H.source,y ∈ Q ↔ (A (H y)).1.1 ≤ 0 ∧ (A (H y)).1.2 ≤ 0)
    (hF : ∀ y ∈ H.source,y ∈ F ↔ (A (H y)).2 = 0) :
    ∃ P : OpenPartialHomeomorph X V3,
      P.source = H.source ∧ x ∈ P.source ∧ P x = 0 ∧
      (∀ i,(e i).symm.trans P ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ P.source,y ∈ (S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)) ↔ P y 1 = 0) ∧
      ∀ y ∈ P.source,y ∈ F ↔ P y 0 = 0 := by
  let HA := H.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hHAs : HA.source = H.source := by
    change H.source ∩ H ⁻¹' univ = H.source
    rw [preimage_univ,inter_univ]
  have hmodel := patch_closures_corner_model HA
    (fun y hy => hS y (hHAs.subset hy)) (fun y hy => hQ y (hHAs.subset hy))
  have hclosure := s.original_ball_patch_replacement_eq_closures u he hd p hp hpi hcontact hdT hSout hTout
  conv at hclosure => rhs; rw [←u.frontier_eq]
  obtain ⟨P,hPs,hxP,hPx,hPe,_,hPS,hPF⟩ := exists_original_corner_pair_chart e H hH A
    (S := (S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q))) hx hHx
    (fun y hy => by rw [hclosure]; exact hmodel y (hHAs.symm.subset hy)) hF
  let L : C3 ≃ₗ[ℝ] V3 := {
    toFun := fun z => ![z.2,z.1.1,z.1.2]
    invFun := fun z => ((z 1,z 2),z 0)
    map_add' := by intros; ext i; fin_cases i <;> rfl
    map_smul' := by intros; ext i; fin_cases i <;> rfl
    left_inv := by intro z; rfl
    right_inv := by intro z; ext i; fin_cases i <;> rfl }
  let M := A.trans L.toContinuousLinearEquiv
  let P' := P.trans M.toHomeomorph.toOpenPartialHomeomorph
  have hP's : P'.source = P.source := by
    change P.source ∩ P ⁻¹' univ = P.source
    rw [preimage_univ,inter_univ]
  have hM : M.toHomeomorph.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 :=
    ⟨locallyPiecewiseAffineOn_affine M.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ,
      locallyPiecewiseAffineOn_affine M.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ⟩
  refine ⟨P',hP's.trans hPs,hP's.symm.subset hxP,?_,?_,?_,?_⟩
  · change M (P x) = 0
    rw [hPx,map_zero]
  · intro i
    simpa only [P',←OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans (hPe i) hM
  · intro y hy
    exact hPS y (hP's.subset hy)
  · intro y hy
    exact hPF y (hP's.subset hy)

end PoincareConjecture.M76
