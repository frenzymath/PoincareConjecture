import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralCapBoundary

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators

universe u

namespace Poincare.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X]

private def vertexMap {m n : Nat} (f : Fin (m + 1) → Fin (n + 1)) :
    C(integralSimplex m, integralSimplex n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

private theorem vertexMap_comp {l m n : Nat}
    (f : Fin (m + 1) → Fin (n + 1)) (g : Fin (l + 1) → Fin (m + 1)) :
    (vertexMap f).comp (vertexMap g) = vertexMap (f ∘ g) := by
  apply ContinuousMap.ext
  intro z
  exact stdSimplex.map_comp_apply g f z

private theorem front_eq (p q : Nat) : integralFrontFace p q =
    vertexMap (Fin.castLE (Nat.le_add_left (q + 1) p)) := rfl

private theorem back_eq (p q : Nat) : integralBackFace p q =
    vertexMap (fun i =>
      Fin.cast (congrArg Nat.succ (Nat.add_comm q p)) (Fin.natAdd q i)) := rfl

private theorem face_eq (n : Nat) (i : Fin (n + 2)) : integralSimplexFace n i =
    vertexMap i.succAbove := rfl

private def vertex {n : Nat} (a : Fin (n + 1)) :
    C(integralSimplex 0, integralSimplex n) := vertexMap ![a]

private def edge {n : Nat} (a b : Fin (n + 1)) :
    C(integralSimplex 1, integralSimplex n) := vertexMap ![a, b]

private def triangle {n : Nat} (a b c : Fin (n + 1)) :
    C(integralSimplex 2, integralSimplex n) := vertexMap ![a, b, c]

private def tetrahedron {n : Nat} (a b c d : Fin (n + 1)) :
    C(integralSimplex 3, integralSimplex n) := vertexMap ![a, b, c, d]

private theorem vertexMap_zero {n : Nat} (f : Fin 1 → Fin (n + 1)) :
    vertexMap f = vertex (f 0) := by
  congr 1
  funext i
  fin_cases i
  rfl

private theorem vertexMap_one {n : Nat} (f : Fin 2 → Fin (n + 1)) :
    vertexMap f = edge (f 0) (f 1) := by
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem vertexMap_two {n : Nat} (f : Fin 3 → Fin (n + 1)) :
    vertexMap f = triangle (f 0) (f 1) (f 2) := by
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem vertexMap_three {n : Nat} (f : Fin 4 → Fin (n + 1)) :
    vertexMap f = tetrahedron (f 0) (f 1) (f 2) (f 3) := by
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem generator_boundary {n : Nat} (s : C(integralSimplex (n + 1), X)) :
    (integralChains X).d (n + 1) n (integralSingularGenerator s (ULift.up 1)) =
      ∑ i : Fin (n + 2), ((-1 : Int) ^ i.val) •
        integralSingularGenerator (s.comp (integralSimplexFace n i)) (ULift.up 1) := by
  let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
      (integralChains X).X n :=
    { toFun := fun f => f.hom (ULift.up 1)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  simpa only [map_sum, map_zsmul, ev] using!
    congrArg ev (integralSingularGenerator_boundary s)

private theorem hom_smul {A B : ModuleCat.{u} Int} (f : A ⟶ B) (a : Int) (z : A) :
    f (a • z) = a • f z := map_zsmul f.hom.toAddMonoidHom a z

private def coeval (q : Nat) (phi : (integralCochains X).X q) :
    (integralChains X).X q →+ Int :=
  (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toAddEquiv.toAddMonoidHom.comp
    (show (integralChains X).X q ⟶ integralCoefficient from phi).hom.toAddMonoidHom

private theorem cap_generator (p q : Nat) (s : C(integralSimplex (p + q), X))
    (phi : (integralCochains X).X q) :
    integralCap p q (integralSingularGenerator s (ULift.up 1)) phi =
      coeval q phi (integralSingularGenerator (s.comp (integralFrontFace p q))
        (ULift.up 1)) •
          integralSingularGenerator (s.comp (integralBackFace p q)) (ULift.up 1) := by
  simpa only [coeval, AddMonoidHom.comp_apply] using! integralCap_generator p q s phi

private theorem coeval_diff (q : Nat) (phi : (integralCochains X).X q)
    (c : (integralChains X).X (q + 1)) :
    coeval (q + 1) ((integralCochains X).d q (q + 1) phi) c =
      coeval q phi ((integralChains X).d (q + 1) q c) := rfl

private theorem cap_four_zero_generator (s : C(integralSimplex 4, X))
    (phi : (integralCochains X).X 0) :
    (integralChains X).d 4 3
      (integralCap 4 0 (integralSingularGenerator s (ULift.up 1)) phi) =
    integralCap 3 0 ((integralChains X).d 4 3
      (integralSingularGenerator s (ULift.up 1))) phi -
    integralCap 3 1 (integralSingularGenerator s (ULift.up 1))
      ((integralCochains X).d 0 1 phi) := by
  rw [cap_generator, generator_boundary, cap_generator]
  simp only [hom_smul, map_sum, LinearMap.sum_apply, coeval_diff]
  rw [generator_boundary (s.comp (integralBackFace 4 0)),
    generator_boundary (s.comp (integralFrontFace 3 1))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, neg_neg,
    one_smul, neg_one_zsmul, map_add, map_neg,
    integralCap_chain_smul 3 0, cap_generator 3 0]
  simp only [front_eq, back_eq, face_eq, ContinuousMap.comp_assoc, vertexMap_comp]
  simp only [vertexMap_zero, vertexMap_three]
  let v (a : Fin 5) := integralSingularGenerator (s.comp (vertex a)) (ULift.up 1)
  let t (a b c d : Fin 5) :=
    integralSingularGenerator (s.comp (tetrahedron a b c d)) (ULift.up 1)
  change coeval 0 phi (v 0) •
      (t 1 2 3 4 + (-t 0 2 3 4 + (t 0 1 3 4 + (-t 0 1 2 4 + t 0 1 2 3)))) =
    (coeval 0 phi (v 1) • t 1 2 3 4 +
      (-(coeval 0 phi (v 0) • t 0 2 3 4) + (coeval 0 phi (v 0) • t 0 1 3 4 +
        (-(coeval 0 phi (v 0) • t 0 1 2 4) + coeval 0 phi (v 0) • t 0 1 2 3)))) -
      (coeval 0 phi (v 1) + -coeval 0 phi (v 0)) • t 1 2 3 4
  simp only [zsmul_add, zsmul_neg, add_zsmul, neg_zsmul]
  abel

private theorem cap_three_two_generator (s : C(integralSimplex 3, X))
    (phi : (integralCochains X).X 2) :
    (integralChains X).d 1 0
      (integralCap 1 2 (integralSingularGenerator s (ULift.up 1)) phi) =
    integralCap 0 2 ((integralChains X).d 3 2
      (integralSingularGenerator s (ULift.up 1))) phi -
    integralCap 0 3 (integralSingularGenerator s (ULift.up 1))
      ((integralCochains X).d 2 3 phi) := by
  rw [cap_generator, generator_boundary, cap_generator]
  simp only [hom_smul, map_sum, LinearMap.sum_apply, coeval_diff]
  rw [generator_boundary (s.comp (integralBackFace 1 2)),
    generator_boundary (s.comp (integralFrontFace 0 3))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, neg_neg,
    one_smul, neg_one_zsmul, map_add, map_neg,
    integralCap_chain_smul 0 2, cap_generator 0 2]
  simp only [front_eq, back_eq, face_eq, ContinuousMap.comp_assoc, vertexMap_comp]
  simp only [vertexMap_zero, vertexMap_two]
  let v (a : Fin 4) := integralSingularGenerator (s.comp (vertex a)) (ULift.up 1)
  let t (a b c : Fin 4) := integralSingularGenerator (s.comp (triangle a b c)) (ULift.up 1)
  change coeval 2 phi (t 0 1 2) • (v 3 + -v 2) =
    (coeval 2 phi (t 1 2 3) • v 3 + (-(coeval 2 phi (t 0 2 3) • v 3) +
      (coeval 2 phi (t 0 1 3) • v 3 + -(coeval 2 phi (t 0 1 2) • v 2)))) -
    (coeval 2 phi (t 1 2 3) + (-coeval 2 phi (t 0 2 3) +
      (coeval 2 phi (t 0 1 3) + -coeval 2 phi (t 0 1 2)))) • v 3
  simp only [zsmul_add, zsmul_neg, add_zsmul, neg_zsmul]
  abel

private theorem cap_four_two_generator (s : C(integralSimplex 4, X))
    (phi : (integralCochains X).X 2) :
    (integralChains X).d 2 1
      (integralCap 2 2 (integralSingularGenerator s (ULift.up 1)) phi) =
    integralCap 1 2 ((integralChains X).d 4 3
      (integralSingularGenerator s (ULift.up 1))) phi -
    integralCap 1 3 (integralSingularGenerator s (ULift.up 1))
      ((integralCochains X).d 2 3 phi) := by
  rw [cap_generator, generator_boundary, cap_generator]
  simp only [hom_smul, map_sum, LinearMap.sum_apply, coeval_diff]
  rw [generator_boundary (s.comp (integralBackFace 2 2)),
    generator_boundary (s.comp (integralFrontFace 1 3))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, neg_neg,
    one_smul, neg_one_zsmul, map_add, map_neg,
    integralCap_chain_smul 1 2, cap_generator 1 2]
  simp only [front_eq, back_eq, face_eq, ContinuousMap.comp_assoc, vertexMap_comp]
  simp only [vertexMap_one, vertexMap_two]
  let e (a b : Fin 5) := integralSingularGenerator (s.comp (edge a b)) (ULift.up 1)
  let t (a b c : Fin 5) := integralSingularGenerator (s.comp (triangle a b c)) (ULift.up 1)
  change coeval 2 phi (t 0 1 2) • (e 3 4 + (-e 2 4 + e 2 3)) =
    (coeval 2 phi (t 1 2 3) • e 3 4 + (-(coeval 2 phi (t 0 2 3) • e 3 4) +
      (coeval 2 phi (t 0 1 3) • e 3 4 + (-(coeval 2 phi (t 0 1 2) • e 2 4) +
        coeval 2 phi (t 0 1 2) • e 2 3)))) -
    (coeval 2 phi (t 1 2 3) + (-coeval 2 phi (t 0 2 3) +
      (coeval 2 phi (t 0 1 3) + -coeval 2 phi (t 0 1 2)))) • e 3 4
  simp only [zsmul_add, zsmul_neg, add_zsmul, neg_zsmul]
  abel

private theorem cap_four_three_generator (s : C(integralSimplex 4, X))
    (phi : (integralCochains X).X 3) :
    (integralChains X).d 1 0
      (integralCap 1 3 (integralSingularGenerator s (ULift.up 1)) phi) =
    integralCap 0 4 (integralSingularGenerator s (ULift.up 1))
      ((integralCochains X).d 3 4 phi) -
    integralCap 0 3 ((integralChains X).d 4 3
      (integralSingularGenerator s (ULift.up 1))) phi := by
  rw [cap_generator, cap_generator, generator_boundary]
  simp only [hom_smul, map_sum, LinearMap.sum_apply, coeval_diff]
  rw [generator_boundary (s.comp (integralBackFace 1 3)),
    generator_boundary (s.comp (integralFrontFace 0 4))]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    pow_zero, pow_succ, mul_neg, mul_one, add_zero, neg_neg,
    one_smul, neg_one_zsmul, map_add, map_neg,
    integralCap_chain_smul 0 3, cap_generator 0 3]
  simp only [front_eq, back_eq, face_eq, ContinuousMap.comp_assoc, vertexMap_comp]
  simp only [vertexMap_zero, vertexMap_three]
  let v (a : Fin 5) := integralSingularGenerator (s.comp (vertex a)) (ULift.up 1)
  let t (a b c d : Fin 5) :=
    integralSingularGenerator (s.comp (tetrahedron a b c d)) (ULift.up 1)
  change coeval 3 phi (t 0 1 2 3) • (v 4 + -v 3) =
    (coeval 3 phi (t 1 2 3 4) + (-coeval 3 phi (t 0 2 3 4) +
      (coeval 3 phi (t 0 1 3 4) + (-coeval 3 phi (t 0 1 2 4) +
        coeval 3 phi (t 0 1 2 3))))) • v 4 -
    (coeval 3 phi (t 1 2 3 4) • v 4 + (-(coeval 3 phi (t 0 2 3 4) • v 4) +
      (coeval 3 phi (t 0 1 3 4) • v 4 + (-(coeval 3 phi (t 0 1 2 4) • v 4) +
        coeval 3 phi (t 0 1 2 3) • v 3))))
  simp only [zsmul_add, zsmul_neg, add_zsmul, neg_zsmul]
  abel

private def capAddHom (p q : Nat) (phi : (integralCochains X).X q) :
    (integralChains X).X (p + q) →+ (integralChains X).X p where
  toFun c := integralCap p q c phi
  map_zero' := by simp only [map_zero, LinearMap.zero_apply]
  map_add' c d := congrArg
    (fun f : (integralCochains X).X q →ₗ[Int] (integralChains X).X p => f phi)
      ((integralCap p q).map_add c d)

private theorem chain_addHom_ext {A : Type u} [AddCommGroup A] (n : Nat)
    (F G : (integralChains X).X n →+ A)
    (h : ∀ s : C(integralSimplex n, X),
      F (integralSingularGenerator s (ULift.up 1)) =
        G (integralSingularGenerator s (ULift.up 1)))
    (c : (integralChains X).X n) : F c = G c := by
  classical
  rw [integral_chain_finite_representation n c]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  let a := integralChainCoordinates X n c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  change F (integralSingularGenerator s a) = G (integralSingularGenerator s a)
  rw [ha, hom_smul, map_zsmul, map_zsmul, h]

theorem integralCap_four_zero_boundary (c : (integralChains X).X 4)
    (phi : (integralCochains X).X 0) :
    (integralChains X).d 4 3 (integralCap 4 0 c phi) =
      integralCap 3 0 ((integralChains X).d 4 3 c) phi -
        integralCap 3 1 c ((integralCochains X).d 0 1 phi) := by
  let d := ((integralChains X).d 4 3).hom.toAddMonoidHom
  exact chain_addHom_ext 4 (d.comp (capAddHom 4 0 phi))
    (((capAddHom 3 0 phi).comp d) - capAddHom 3 1 ((integralCochains X).d 0 1 phi))
    (fun s => cap_four_zero_generator s phi) c

theorem integralCap_three_two_boundary (c : (integralChains X).X 3)
    (phi : (integralCochains X).X 2) :
    (integralChains X).d 1 0 (integralCap 1 2 c phi) =
      integralCap 0 2 ((integralChains X).d 3 2 c) phi -
        integralCap 0 3 c ((integralCochains X).d 2 3 phi) := by
  let d := ((integralChains X).d 3 2).hom.toAddMonoidHom
  exact chain_addHom_ext 3 (((integralChains X).d 1 0).hom.toAddMonoidHom.comp
    (capAddHom 1 2 phi))
    (((capAddHom 0 2 phi).comp d) - capAddHom 0 3 ((integralCochains X).d 2 3 phi))
    (fun s => cap_three_two_generator s phi) c

theorem integralCap_four_two_boundary (c : (integralChains X).X 4)
    (phi : (integralCochains X).X 2) :
    (integralChains X).d 2 1 (integralCap 2 2 c phi) =
      integralCap 1 2 ((integralChains X).d 4 3 c) phi -
        integralCap 1 3 c ((integralCochains X).d 2 3 phi) := by
  let d := ((integralChains X).d 4 3).hom.toAddMonoidHom
  exact chain_addHom_ext 4 (((integralChains X).d 2 1).hom.toAddMonoidHom.comp
    (capAddHom 2 2 phi))
    (((capAddHom 1 2 phi).comp d) - capAddHom 1 3 ((integralCochains X).d 2 3 phi))
    (fun s => cap_four_two_generator s phi) c

theorem integralCap_four_three_boundary (c : (integralChains X).X 4)
    (phi : (integralCochains X).X 3) :
    (integralChains X).d 1 0 (integralCap 1 3 c phi) =
      integralCap 0 4 c ((integralCochains X).d 3 4 phi) -
        integralCap 0 3 ((integralChains X).d 4 3 c) phi := by
  let d := ((integralChains X).d 4 3).hom.toAddMonoidHom
  exact chain_addHom_ext 4 (((integralChains X).d 1 0).hom.toAddMonoidHom.comp
    (capAddHom 1 3 phi))
    (capAddHom 0 4 ((integralCochains X).d 3 4 phi) - (capAddHom 0 3 phi).comp d)
    (fun s => cap_four_three_generator s phi) c

end

end Poincare.Topology
