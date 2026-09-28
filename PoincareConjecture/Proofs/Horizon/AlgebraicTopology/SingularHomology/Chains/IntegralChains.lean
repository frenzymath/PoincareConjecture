import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Subdivision.SingularHomologyClass
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.ULift










set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace Poincare.Topology


noncomputable def integralCoefficientHomEquiv (M : ModuleCat.{w} ℤ) :
    (ModuleCat.of ℤ (ULift.{w} ℤ) ⟶ M) ≃+ M :=
  ModuleCat.homAddEquiv.trans
    ((LinearEquiv.congrLeft M ℕ (ULift.moduleEquiv : ULift.{w} ℤ ≃ₗ[ℤ] ℤ)).toAddEquiv.trans
      (LinearMap.ringLmapEquivSelf ℤ ℕ M).toAddEquiv)

theorem integralCoefficientHomEquiv_apply (M : ModuleCat.{w} ℤ)
    (f : ModuleCat.of ℤ (ULift.{w} ℤ) ⟶ M) :
    integralCoefficientHomEquiv M f = f (ULift.up 1) := rfl

theorem integralCoefficientHomEquiv_symm_apply (M : ModuleCat.{w} ℤ)
    (m : M) (a : ULift.{w} ℤ) :
    (integralCoefficientHomEquiv M).symm m a = a.down • m := by
  let f := (integralCoefficientHomEquiv M).symm m
  have ha : a = a.down • (ULift.up (1 : ℤ) : ULift.{w} ℤ) := by
    apply ULift.ext
    simp
  have hf : f (ULift.up 1) = m := (integralCoefficientHomEquiv M).apply_symm_apply m
  calc
    f a = f (a.down • (ULift.up (1 : ℤ) : ULift.{w} ℤ)) := congrArg f ha
    _ = a.down • f (ULift.up 1) := map_zsmul f.hom.toAddMonoidHom _ _
    _ = a.down • m := congrArg (a.down • ·) hf


theorem exists_integral_simplicial_chain_coefficients (X : SSet.{w}) (n : ℕ)
    (z : ModuleCat.of ℤ (ULift.{w} ℤ) ⟶
      (X.chainComplex (ModuleCat.of ℤ (ULift.{w} ℤ))).X n) :
    ∃ a : (X _⦋n⦌) →₀ ℤ, z = ∑ s ∈ a.support, a s • X.ιChainComplex s := by
  classical
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let e : (X.chainComplex R).X n ≅
      ModuleCat.of ℤ ((X _⦋n⦌) →₀ ULift.{w} ℤ) :=
    (X.isColimitChainComplexXCofan R n).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{w} ℤ) (X _⦋n⦌))
  have hι (s : X _⦋n⦌) : X.ιChainComplex (R := R) s ≫ e.hom =
      ModuleCat.ofHom (Finsupp.lsingle s (R := ℤ) (M := ULift.{w} ℤ)) :=
    (X.isColimitChainComplexXCofan R n).comp_coconePointUniqueUpToIso_hom
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{w} ℤ) (X _⦋n⦌)) ⟨s⟩
  let a0 : (X _⦋n⦌) →₀ ULift.{w} ℤ := integralCoefficientHomEquiv _ (z ≫ e.hom)
  let a : (X _⦋n⦌) →₀ ℤ := a0.mapRange ULift.down rfl
  refine ⟨a, ?_⟩
  apply (cancel_mono e.hom).mp
  apply (integralCoefficientHomEquiv _).injective
  change a0 = integralCoefficientHomEquiv _ ((∑ s ∈ a.support, a s • X.ιChainComplex s) ≫ e.hom)
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hι, map_sum, map_zsmul]
  change a0 = a.sum (fun s b => b • Finsupp.single s (ULift.up (1 : ℤ)))
  rw [show a.sum (fun s b => b • Finsupp.single s (ULift.up (1 : ℤ))) =
      a0.sum (fun s b => b.down • Finsupp.single s (ULift.up (1 : ℤ))) from
    Finsupp.sum_mapRange_index (fun _ => zero_smul _ _)]
  calc
    a0 = a0.sum Finsupp.single := (Finsupp.sum_single a0).symm
    _ = _ := by
      apply Finsupp.sum_congr
      intro s hs
      rw [Finsupp.smul_single]
      congr 1
      apply ULift.ext
      simp


theorem exists_integral_simplicial_homology_cycle (X : SSet.{w}) (n : ℕ)
    (h : ModuleCat.of ℤ (ULift.{w} ℤ) ⟶
      X.homology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) :
    ∃ z : ModuleCat.of ℤ (ULift.{w} ℤ) ⟶
        (X.chainComplex (ModuleCat.of ℤ (ULift.{w} ℤ))).X (n + 1),
      ∃ hz : z ≫ (X.chainComplex (ModuleCat.of ℤ (ULift.{w} ℤ))).d (n + 1) n = 0,
        (X.chainComplex (ModuleCat.of ℤ (ULift.{w} ℤ))).liftCycles z n (by simp) hz ≫
          (X.chainComplex (ModuleCat.of ℤ (ULift.{w} ℤ))).homologyπ (n + 1) = h := by
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let K := X.chainComplex R
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n + 1))).mp inferInstance
    (h (ULift.up 1))
  let u : R ⟶ K.cycles (n + 1) :=
    (integralCoefficientHomEquiv (K.cycles (n + 1))).symm y
  let z := u ≫ K.iCycles (n + 1)
  have hz : z ≫ K.d (n + 1) n = 0 := by
    simp only [z, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  refine ⟨z, hz, ?_⟩
  have hlift : K.liftCycles z n (by simp) hz = u := by
    apply (cancel_mono (K.iCycles (n + 1))).mp
    rw [HomologicalComplex.liftCycles_i]
  rw [hlift]
  apply (integralCoefficientHomEquiv _).injective
  change K.homologyπ (n + 1) (u (ULift.up 1)) = h (ULift.up 1)
  have hu : u (ULift.up 1) = y :=
    (integralCoefficientHomEquiv (K.cycles (n + 1))).apply_symm_apply y
  rw [hu]
  exact hy


theorem singularHomologyMap_const_eq_zero
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    [CategoryWithHomology C] (R : C) (X Y : TopCat.{w}) (n : ℕ) (y : Y) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const X y)))
      R (n + 1) = 0 := by
  let P : TopCat.{w} := TopCat.of (PUnit.{w + 1})
  let f : X ⟶ P := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let g : P ⟶ Y := TopCat.ofHom (ContinuousMap.const P y)
  have hfg : f ≫ g = TopCat.ofHom (ContinuousMap.const X y) := rfl
  rw [← hfg, Functor.map_comp, SSet.homologyMap_comp]
  have hzero : IsZero ((TopCat.toSSet.obj P).homology R (n + 1)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      C (n + 1) R P (Nat.succ_ne_zero n)
  rw [hzero.eq_of_tgt (SSet.homologyMap (TopCat.toSSet.map f) R (n + 1)) 0, zero_comp]

end Poincare.Topology
