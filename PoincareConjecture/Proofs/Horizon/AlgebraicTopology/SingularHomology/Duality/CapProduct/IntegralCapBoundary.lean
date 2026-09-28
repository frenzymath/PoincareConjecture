import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapChains








set_option autoImplicit false

open CategoryTheory
open scoped BigOperators

universe u
namespace Poincare.Topology
noncomputable section
variable {X : Type u} [TopologicalSpace X]

private def simplexVertexMap {m n : Nat} (f : Fin (m + 1) -> Fin (n + 1)) :
    C(integralSimplex m, integralSimplex n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

private theorem simplexVertexMap_comp {l m n : Nat}
    (f : Fin (m + 1) -> Fin (n + 1)) (g : Fin (l + 1) -> Fin (m + 1)) :
    (simplexVertexMap f).comp (simplexVertexMap g) = simplexVertexMap (f ∘ g) := by
  apply ContinuousMap.ext
  intro z
  exact stdSimplex.map_comp_apply g f z

private theorem front_eq (p q : Nat) : integralFrontFace p q =
    simplexVertexMap (Fin.castLE (Nat.le_add_left (q + 1) p)) := rfl
private theorem back_eq (p q : Nat) : integralBackFace p q =
    simplexVertexMap (fun i =>
      Fin.cast (congrArg Nat.succ (Nat.add_comm q p)) (Fin.natAdd q i)) := rfl
private theorem face_eq (n : Nat) (i : Fin (n + 2)) : integralSimplexFace n i =
    simplexVertexMap i.succAbove := rfl

private def simplexEdge {n : Nat} (a b : Fin (n + 1)) :
    C(integralSimplex 1, integralSimplex n) := simplexVertexMap ![a, b]

private theorem simplexVertexMap_edge {n : Nat} (f : Fin 2 -> Fin (n + 1)) :
    simplexVertexMap f = simplexEdge (f 0) (f 1) := by
  apply congrArg simplexVertexMap
  funext i
  fin_cases i <;> rfl

private def simplexVertex {n : Nat} (a : Fin (n + 1)) :
    C(integralSimplex 0, integralSimplex n) := simplexVertexMap ![a]

private theorem simplexVertexMap_vertex {n : Nat} (f : Fin 1 -> Fin (n + 1)) :
    simplexVertexMap f = simplexVertex (f 0) := by
  apply congrArg simplexVertexMap
  funext i
  fin_cases i
  rfl

private def simplexTriangle {n : Nat} (a b c : Fin (n + 1)) :
    C(integralSimplex 2, integralSimplex n) := simplexVertexMap ![a, b, c]

private theorem simplexVertexMap_triangle {n : Nat} (f : Fin 3 -> Fin (n + 1)) :
    simplexVertexMap f = simplexTriangle (f 0) (f 1) (f 2) := by
  apply congrArg simplexVertexMap
  funext i
  fin_cases i <;> rfl

private theorem generator_boundary_apply {n : Nat} (s : C(integralSimplex (n + 1), X)) :
    (integralChains X).d (n + 1) n (integralSingularGenerator s (ULift.up 1)) =
      ∑ i : Fin (n + 2), ((-1 : Int) ^ i.val) •
        (integralSingularGenerator (s.comp (integralSimplexFace n i)) (ULift.up 1)) := by
  let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
      (integralChains X).X n :=
    { toFun := fun f => f.hom (ULift.up 1)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg ev (integralSingularGenerator_boundary s)
  simpa [map_sum, map_zsmul, ev] using! h

private theorem integralHom_smul {A B : ModuleCat.{u} Int} (f : A ⟶ B) (a : Int) (z : A) :
    f (a • z) = a • f z := map_zsmul f.hom.toAddMonoidHom a z

theorem integralCap_chain_smul (p q : Nat) (a : Int) (c : (integralChains X).X (p + q))
    (phi : (integralCochains X).X q) :
    integralCap p q (a • c) phi = a • (integralCap p q c phi) := by
  have h := map_zsmul (integralCap (X := X) p q).toAddMonoidHom a c
  exact congrArg (fun f : (integralCochains X).X q →ₗ[Int] (integralChains X).X p =>
    f phi) h

private def cochainEval (q : Nat) (phi : (integralCochains X).X q) :
    (integralChains X).X q →+ Int :=
  (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toAddEquiv.toAddMonoidHom.comp
    (show (integralChains X).X q ⟶ integralCoefficient from phi).hom.toAddMonoidHom

private theorem cap_generator' (p q : Nat)
    (s : C(integralSimplex (p + q), X)) (phi : (integralCochains X).X q) :
    integralCap p q (integralSingularGenerator s (ULift.up 1)) phi =
      cochainEval q phi (integralSingularGenerator (s.comp (integralFrontFace p q))
        (ULift.up 1)) •
          (integralSingularGenerator (s.comp (integralBackFace p q)) (ULift.up 1)) := by
  simpa only [cochainEval, AddMonoidHom.comp_apply] using! integralCap_generator p q s phi

private theorem cochainEval_diff (q : Nat) (phi : (integralCochains X).X q)
    (c : (integralChains X).X (q + 1)) :
    cochainEval (q + 1) ((integralCochains X).d q (q + 1) phi) c =
      cochainEval q phi ((integralChains X).d (q + 1) q c) := rfl

private theorem cap_algebra {A : Type*} [AddCommGroup A] (a b c : Int) (u v w : A) :
    a • (u + (-v + w)) =
      (b + (-c + a)) • u -
        (b • u + (-(c • u) + (a • v + -(a • w)))) := by
  simp only [zsmul_add, zsmul_neg, add_zsmul, neg_zsmul]
  abel

private theorem cap_three_one_generator (s : C(integralSimplex 3, X))
    (phi : (integralCochains X).X 1) :
    (integralChains X).d 2 1
        (integralCap 2 1 (integralSingularGenerator s (ULift.up 1)) phi) =
      integralCap 1 2 (integralSingularGenerator s (ULift.up 1))
          ((integralCochains X).d 1 2 phi) -
        integralCap 1 1 ((integralChains X).d 3 2
          (integralSingularGenerator s (ULift.up 1))) phi := by
  rw [cap_generator', cap_generator', generator_boundary_apply]
  simp only [integralHom_smul, map_sum, LinearMap.sum_apply, cochainEval_diff]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, one_smul]
  rw [generator_boundary_apply (s.comp (integralBackFace 2 1)),
    generator_boundary_apply (s.comp (integralFrontFace 1 2))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, neg_neg,
    one_smul, map_add, integralCap_chain_smul 1 1, cap_generator' 1 1]
  simp only [front_eq, back_eq, face_eq, ContinuousMap.comp_assoc, simplexVertexMap_comp,
    neg_one_zsmul, map_neg]
  simp only [simplexVertexMap_edge]
  let e (a b : Fin 4) : (integralChains X).X 1 :=
    integralSingularGenerator (s.comp (simplexEdge a b)) (ULift.up 1)
  change (cochainEval 1 phi (e 0 1)) • (e 2 3 + (-e 1 3 + e 1 2)) =
    (cochainEval 1 phi (e 1 2) + (-cochainEval 1 phi (e 0 2) +
      cochainEval 1 phi (e 0 1))) • e 2 3 -
    (cochainEval 1 phi (e 1 2) • e 2 3 +
      (-(cochainEval 1 phi (e 0 2) • e 2 3) +
        (cochainEval 1 phi (e 0 1) • e 1 3 +
          -(cochainEval 1 phi (e 0 1) • e 1 2))))
  exact cap_algebra _ _ _ _ _ _

private theorem cap_algebra_four {A : Type*} [AddCommGroup A]
    (a b c : Int) (u v w z : A) :
    a • (u + (-v + (w + -z))) =
      (b + (-c + a)) • u -
        (b • u + (-(c • u) + (a • v + (-(a • w) + a • z)))) := by
  simp only [zsmul_add, zsmul_neg, add_zsmul, neg_zsmul]
  abel

private theorem cap_four_one_generator (s : C(integralSimplex 4, X))
    (phi : (integralCochains X).X 1) :
    (integralChains X).d 3 2
        (integralCap 3 1 (integralSingularGenerator s (ULift.up 1)) phi) =
      integralCap 2 2 (integralSingularGenerator s (ULift.up 1))
          ((integralCochains X).d 1 2 phi) -
        integralCap 2 1 ((integralChains X).d 4 3
          (integralSingularGenerator s (ULift.up 1))) phi := by
  rw [cap_generator', cap_generator', generator_boundary_apply]
  simp only [integralHom_smul, map_sum, LinearMap.sum_apply, cochainEval_diff]
  rw [generator_boundary_apply (s.comp (integralBackFace 3 1)),
    generator_boundary_apply (s.comp (integralFrontFace 2 2))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, neg_neg,
    one_smul, neg_one_zsmul, map_add, map_neg,
    integralCap_chain_smul 2 1, cap_generator' 2 1]
  simp only [front_eq, back_eq, face_eq, ContinuousMap.comp_assoc, simplexVertexMap_comp]
  simp only [simplexVertexMap_edge, simplexVertexMap_triangle]
  let e (a b : Fin 5) : (integralChains X).X 1 :=
    integralSingularGenerator (s.comp (simplexEdge a b)) (ULift.up 1)
  let t (a b c : Fin 5) : (integralChains X).X 2 :=
    integralSingularGenerator (s.comp (simplexTriangle a b c)) (ULift.up 1)
  change (cochainEval 1 phi (e 0 1)) • (t 2 3 4 + (-t 1 3 4 + (t 1 2 4 + -t 1 2 3))) =
    (cochainEval 1 phi (e 1 2) + (-cochainEval 1 phi (e 0 2) +
      cochainEval 1 phi (e 0 1))) • t 2 3 4 -
    (cochainEval 1 phi (e 1 2) • t 2 3 4 +
      (-(cochainEval 1 phi (e 0 2) • t 2 3 4) +
        (cochainEval 1 phi (e 0 1) • t 1 3 4 +
          (-(cochainEval 1 phi (e 0 1) • t 1 2 4) +
            cochainEval 1 phi (e 0 1) • t 1 2 3))))
  exact cap_algebra_four _ _ _ _ _ _ _

private theorem cap_algebra_zero {A : Type*} [AddCommGroup A]
    (a b : Int) (u v w z : A) :
    a • (u + (-v + (w + -z))) =
      (b • u + (-(a • v) + (a • w + -(a • z)))) - (b + -a) • u := by
  simp only [zsmul_add, zsmul_neg, add_zsmul, neg_zsmul]
  abel

private theorem cap_three_zero_generator (s : C(integralSimplex 3, X))
    (phi : (integralCochains X).X 0) :
    (integralChains X).d 3 2
        (integralCap 3 0 (integralSingularGenerator s (ULift.up 1)) phi) =
      integralCap 2 0 ((integralChains X).d 3 2
          (integralSingularGenerator s (ULift.up 1))) phi -
        integralCap 2 1 (integralSingularGenerator s (ULift.up 1))
          ((integralCochains X).d 0 1 phi) := by
  rw [cap_generator', generator_boundary_apply, cap_generator']
  simp only [integralHom_smul, map_sum, LinearMap.sum_apply, cochainEval_diff]
  rw [generator_boundary_apply (s.comp (integralBackFace 3 0)),
    generator_boundary_apply (s.comp (integralFrontFace 2 1))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, neg_neg,
    one_smul, neg_one_zsmul, map_add, map_neg,
    integralCap_chain_smul 2 0, cap_generator' 2 0]
  simp only [front_eq, back_eq, face_eq, ContinuousMap.comp_assoc, simplexVertexMap_comp]
  simp only [simplexVertexMap_vertex, simplexVertexMap_triangle]
  let v (a : Fin 4) : (integralChains X).X 0 :=
    integralSingularGenerator (s.comp (simplexVertex a)) (ULift.up 1)
  let t (a b c : Fin 4) : (integralChains X).X 2 :=
    integralSingularGenerator (s.comp (simplexTriangle a b c)) (ULift.up 1)
  change cochainEval 0 phi (v 0) • (t 1 2 3 + (-t 0 2 3 + (t 0 1 3 + -t 0 1 2))) =
    (cochainEval 0 phi (v 1) • t 1 2 3 +
      (-(cochainEval 0 phi (v 0) • t 0 2 3) +
        (cochainEval 0 phi (v 0) • t 0 1 3 + -(cochainEval 0 phi (v 0) • t 0 1 2)))) -
    (cochainEval 0 phi (v 1) + -cochainEval 0 phi (v 0)) • t 1 2 3
  exact cap_algebra_zero _ _ _ _ _ _

theorem integralCap_three_one_boundary (c : (integralChains X).X 3)
    (phi : (integralCochains X).X 1) :
    (integralChains X).d 2 1 (integralCap 2 1 c phi) =
      integralCap 1 2 c ((integralCochains X).d 1 2 phi) -
        integralCap 1 1 ((integralChains X).d 3 2 c) phi := by
  classical
  rw [integral_chain_finite_representation 3 c]
  simp only [map_sum, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  let a := integralChainCoordinates X 3 c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : integralSingularGenerator s a =
      a.down • (integralSingularGenerator s (ULift.up 1)) := by
    conv_lhs => rw [ha, integralHom_smul]
  change (integralChains X).d 2 1 (integralCap 2 1 (integralSingularGenerator s a) phi) =
    integralCap 1 2 (integralSingularGenerator s a) ((integralCochains X).d 1 2 phi) -
      integralCap 1 1 ((integralChains X).d 3 2 (integralSingularGenerator s a)) phi
  rw [hg, integralCap_chain_smul, integralHom_smul, cap_three_one_generator,
    integralCap_chain_smul, integralHom_smul, integralCap_chain_smul, zsmul_sub]

theorem integralCap_four_one_boundary (c : (integralChains X).X 4)
    (phi : (integralCochains X).X 1) :
    (integralChains X).d 3 2 (integralCap 3 1 c phi) =
      integralCap 2 2 c ((integralCochains X).d 1 2 phi) -
        integralCap 2 1 ((integralChains X).d 4 3 c) phi := by
  classical
  rw [integral_chain_finite_representation 4 c]
  simp only [map_sum, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  let a := integralChainCoordinates X 4 c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : integralSingularGenerator s a =
      a.down • (integralSingularGenerator s (ULift.up 1)) := by
    conv_lhs => rw [ha, integralHom_smul]
  change (integralChains X).d 3 2 (integralCap 3 1 (integralSingularGenerator s a) phi) =
    integralCap 2 2 (integralSingularGenerator s a) ((integralCochains X).d 1 2 phi) -
      integralCap 2 1 ((integralChains X).d 4 3 (integralSingularGenerator s a)) phi
  rw [hg, integralCap_chain_smul, integralHom_smul, cap_four_one_generator,
    integralCap_chain_smul, integralHom_smul, integralCap_chain_smul, zsmul_sub]

theorem integralCap_three_zero_boundary (c : (integralChains X).X 3)
    (phi : (integralCochains X).X 0) :
    (integralChains X).d 3 2 (integralCap 3 0 c phi) =
      integralCap 2 0 ((integralChains X).d 3 2 c) phi -
        integralCap 2 1 c ((integralCochains X).d 0 1 phi) := by
  classical
  rw [integral_chain_finite_representation 3 c]
  simp only [map_sum, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  let a := integralChainCoordinates X 3 c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : integralSingularGenerator s a =
      a.down • (integralSingularGenerator s (ULift.up 1)) := by
    conv_lhs => rw [ha, integralHom_smul]
  change (integralChains X).d 3 2 (integralCap 3 0 (integralSingularGenerator s a) phi) =
    integralCap 2 0 ((integralChains X).d 3 2 (integralSingularGenerator s a)) phi -
      integralCap 2 1 (integralSingularGenerator s a) ((integralCochains X).d 0 1 phi)
  rw [hg, integralCap_chain_smul, integralHom_smul, cap_three_zero_generator,
    integralHom_smul, integralCap_chain_smul, integralCap_chain_smul, zsmul_sub]

end
end Poincare.Topology
