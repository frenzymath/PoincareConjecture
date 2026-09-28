import PoincareConjecture.Proofs.M02.SimplexCompression
import PoincareConjecture.Proofs.M02.SimplexFamilyHomology
import PoincareConjecture.Proofs.M02.HurewiczAdditivity
import PoincareConjecture.Proofs.M02.SimplexRepresentatives
import PoincareConjecture.Proofs.M02.IntegralChains
import PoincareConjecture.Proofs.M02.CubeSphere
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected









set_option autoImplicit false

open CategoryTheory Limits Set Topology
open scoped Simplicial Topology unitInterval

universe w v u

namespace PoincareConjecture.Proofs.M02



theorem homotopyGroupSingularHomologyMap_surjective (X : TopCat.{w})
    [PathConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ n → Subsingleton (HomotopyGroup.Pi k X x)) :
    Function.Surjective
      (homotopyGroupSingularHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) X n x) := by
  classical
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let Y := TopCat.toSSet.obj X
  obtain ⟨K, r, H, _hcoh, hface, htrace⟩ :=
    exists_singularSimplex_straightening X x n hpi
  let F := homotopyGroupSingularHomologyHom R X n x
  let S := F.range.toAddSubgroup'
  let c (s : Y _⦋n + 1⦌) := singularSimplexHomologyClass R X (r s) x (hface s)
  have hc (s : Y _⦋n + 1⦌) : c s ∈ S := by
    obtain ⟨p, hp⟩ := exists_genLoop_of_singularSimplex_constant_faces
      X n (r s) x (hface s)
    change Multiplicative.ofAdd (c s) ∈ F.range
    apply MonoidHom.mem_range.mpr
    refine ⟨⟦p⟧, ?_⟩
    change Multiplicative.ofAdd (genLoopSingularHomologyClass R X p) =
      Multiplicative.ofAdd (c s)
    congr 1
    simp only [genLoopSingularHomologyClass, c, hp]
  intro h
  obtain ⟨z, hz, hzh⟩ := exists_integral_simplicial_homology_cycle Y n h
  have hf := singularSimplexFamily_cycle_homology_factorization R X x r H
    (K n (Nat.le_refl n)) hface htrace z hz
  obtain ⟨a, ha⟩ := exists_integral_simplicial_chain_coefficients Y (n + 1) z
  let D : (Y.chainComplex R).X (n + 1) ⟶
      (Y.chainComplex R).homology (n + 1) :=
    Sigma.desc (fun s => singularSimplexHomologyClass R X (r s) x (hface s))
  have hf' :
      (Y.chainComplex R).liftCycles z n (by simp) hz ≫
          (Y.chainComplex R).homologyπ (n + 1) = z ≫ D := by
    simpa only [D] using hf
  have hsum : h = ∑ s ∈ a.support, a s • c s := by
    rw [← hzh, hf', ha]
    rw [Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Preadditive.zsmul_comp]
    change a j • (Sigma.ι (fun _ => R) j ≫
      Sigma.desc (fun s => singularSimplexHomologyClass R X (r s) x (hface s))) = _
    congr 1
    exact Sigma.ι_desc _ _
  have hh : h ∈ S := by
    rw [hsum]
    exact S.sum_mem fun s hs => S.zsmul_mem (hc s) (a s)
  obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp hh
  exact ⟨q, congrArg Multiplicative.toAdd hq⟩



theorem isZero_integral_singularHomology_of_homotopy_vanishing (X : TopCat.{w})
    [PathConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ n + 1 → Subsingleton (HomotopyGroup.Pi k X x)) :
    IsZero ((TopCat.toSSet.obj X).homology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) := by
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let M := (TopCat.toSSet.obj X).homology R (n + 1)
  let e := integralCoefficientHomEquiv M
  have hs := homotopyGroupSingularHomologyMap_surjective X x n
    (fun k hk hkn => hpi k hk (Nat.le_trans hkn (Nat.le_succ n)))
  let := hpi (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => ?_⟩
  obtain ⟨p, hp⟩ := hs (e.symm a)
  obtain ⟨q, hq⟩ := hs (e.symm b)
  apply e.symm.injective
  rw [← hp, ← hq, Subsingleton.elim p q]



theorem isZero_integral_singularHomology_one (X : TopCat.{w}) [SimplyConnectedSpace X] :
    IsZero ((TopCat.toSSet.obj X).homology
      (ModuleCat.of ℤ (ULift.{w} ℤ)) 1) := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  apply isZero_integral_singularHomology_of_homotopy_vanishing X x 0
  intro k hk hk1
  have hk' : k = 1 := by omega
  subst k
  exact ⟨fun p q => HomotopyGroup.pi1EquivFundamentalGroup.injective
    (Subsingleton.elim _ _)⟩



theorem exists_quotient_integral_homology_representatives (X : TopCat.{w})
    [PathConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ n → Subsingleton (HomotopyGroup.Pi k X x))
    (Q : TopCat.{w}) (q : C(I^(Fin (n + 1)), Q)) (hq : IsQuotientMap q)
    (hfib : ∀ z w, q z = q w ↔ z = w ∨
      (z ∈ Cube.boundary (Fin (n + 1)) ∧ w ∈ Cube.boundary (Fin (n + 1)))) :
    let R := ModuleCat.of ℤ (ULift.{w} ℤ)
    ∃ p0 : GenLoop (Fin (n + 1)) Q (q (fun _ => 0)), p0.val = q ∧
      ∀ h : R ⟶ (TopCat.toSSet.obj X).homology R (n + 1),
        ∃ f : Q ⟶ X, f (q (fun _ => 0)) = x ∧
          genLoopSingularHomologyClass R Q p0 ≫
            SSet.homologyMap (TopCat.toSSet.map f) R (n + 1) = h := by
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let p0 : GenLoop (Fin (n + 1)) Q (q (fun _ => 0)) := ⟨q, fun z hz =>
    (hfib z (fun _ => 0)).mpr (Or.inr ⟨hz, ⟨0, Or.inl rfl⟩⟩)⟩
  refine ⟨p0, rfl, ?_⟩
  intro h
  obtain ⟨a, ha⟩ := homotopyGroupSingularHomologyMap_surjective X x n hpi h
  obtain ⟨p, rfl⟩ := Quotient.exists_rep a
  obtain ⟨f0, hcomp, hbase⟩ := exists_genLoop_quotient_map n q hq hfib p
  let f : Q ⟶ X := TopCat.ofHom f0
  have hbase' : f (q (fun _ => 0)) = x := hbase
  refine ⟨f, hbase, ?_⟩
  have hs : (TopCat.toSSet.map f).app _ (genLoopSingularSimplex Q p0) =
      genLoopSingularSimplex X p := by
    apply (X.toSSetObjEquiv _).injective
    ext z
    change f0 (q ((Classical.choose (exists_stdSimplex_cube_pair_homeomorph (n + 1))) z)) =
      p ((Classical.choose (exists_stdSimplex_cube_pair_homeomorph (n + 1))) z)
    exact ContinuousMap.congr_fun hcomp _
  have hnat := singularSimplexHomologyClass_naturality R f
    (genLoopSingularSimplex Q p0) (q (fun _ => 0)) (genLoopSingularSimplex_face Q p0)
  have hclass : genLoopSingularHomologyClass R Q p0 ≫
      SSet.homologyMap (TopCat.toSSet.map f) R (n + 1) =
        genLoopSingularHomologyClass R X p := by
    simpa only [genLoopSingularHomologyClass, hs, hbase'] using hnat
  exact hclass.trans ha



theorem exists_sphere_class_representing_integral_homology (X : TopCat.{w})
    [PathConnectedSpace X] (x : X) (n : ℕ)
    (hpi : ∀ (k : ℕ), 1 ≤ k → k ≤ n → Subsingleton (HomotopyGroup.Pi k X x)) :
    let Q : TopCat.{w} :=
      TopCat.of (ULift.{w} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1))
    let R := ModuleCat.of ℤ (ULift.{w} ℤ)
    ∃ (y : Q) (a : R ⟶ (TopCat.toSSet.obj Q).homology R (n + 1)),
      ∀ h : R ⟶ (TopCat.toSSet.obj X).homology R (n + 1),
        ∃ f : Q ⟶ X, f y = x ∧
          a ≫ SSet.homologyMap (TopCat.toSSet.map f) R (n + 1) = h := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1
  let Q : TopCat.{w} := TopCat.of (ULift.{w} S)
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let e : Q ≃ₜ S := Homeomorph.ulift
  obtain ⟨q, hq, hfib⟩ := exists_cube_sphere_quotient_of_card_eq
    (N := Fin (n + 1)) (ι := Fin (n + 2)) (by simp [Nat.add_assoc])
  let q' : C(I^(Fin (n + 1)), Q) := (⟨e.symm, e.symm.continuous⟩ : C(S, Q)).comp q
  have hq' : IsQuotientMap q' := IsQuotientMap.of_surjective_continuous
    (e.symm.surjective.comp hq.surjective) q'.continuous
  have hfib' (z w : I^(Fin (n + 1))) : q' z = q' w ↔ z = w ∨
      (z ∈ Cube.boundary (Fin (n + 1)) ∧ w ∈ Cube.boundary (Fin (n + 1))) := by
    change e.symm (q z) = e.symm (q w) ↔ _
    rw [e.symm.injective.eq_iff]
    exact hfib z w
  obtain ⟨p0, _hp0, hrep⟩ := exists_quotient_integral_homology_representatives
    X x n hpi Q q' hq' hfib'
  exact ⟨q' (fun _ => 0), genLoopSingularHomologyClass R Q p0, hrep⟩

end PoincareConjecture.Proofs.M02
