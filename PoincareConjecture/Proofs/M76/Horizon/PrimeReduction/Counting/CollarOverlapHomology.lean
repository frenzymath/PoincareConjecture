import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ModTwoMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Subdivision.SingularOneCocycles
import Mathlib.Topology.ContinuousMap.Sigma








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open Poincare.Topology
open scoped Simplicial BigOperators

universe u v

namespace PoincareConjecture.M76.CollarOverlap

theorem sigma_one_cocycle_is_coboundary
    {I : Type u} (Y : I → Type u) [∀ i, TopologicalSpace (Y i)]
    [∀ i, SimplyConnectedSpace (Y i)]
    {G : Type v} [AddCommGroup G]
    (f : (TopCat.toSSet.obj (TopCat.of (Σ i, Y i))) _⦋1⦌ → G)
    (hf : ∀ s : (TopCat.toSSet.obj (TopCat.of (Σ i, Y i))) _⦋2⦌,
      (∑ j : Fin 3, ((-1 : ℤ) ^ j.val) •
        f ((TopCat.toSSet.obj (TopCat.of (Σ i, Y i))).δ j s)) = 0) :
    ∃ g : (TopCat.toSSet.obj (TopCat.of (Σ i, Y i))) _⦋0⦌ → G,
      ∀ s, f s = g ((TopCat.toSSet.obj (TopCat.of (Σ i, Y i))).δ 0 s) -
        g ((TopCat.toSSet.obj (TopCat.of (Σ i, Y i))).δ 1 s) := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of (Σ i, Y i))
  let Si (i : I) := TopCat.toSSet.obj (TopCat.of (Y i))
  let j (i : I) : Si i ⟶ S := TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.sigmaMk i))
  have hi (i : I) : ∃ g : Si i _⦋0⦌ → G, ∀ s : Si i _⦋1⦌,
      f ((j i).app _ s) = g ((Si i).δ 0 s) - g ((Si i).δ 1 s) := by
    apply singular_one_cocycle_is_coboundary (TopCat.of (Y i))
    intro s
    have hj (k : Fin 3) : (j i).app _ ((Si i).δ k s) = S.δ k ((j i).app _ s) :=
      congrArg (fun h => h s) ((j i).naturality (SimplexCategory.δ k).op)
    calc
      _ = ∑ k : Fin 3, ((-1 : ℤ) ^ k.val) • f (S.δ k ((j i).app _ s)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact congrArg (fun z => ((-1 : ℤ) ^ k.val) • f z) (hj k)
      _ = 0 := hf ((j i).app _ s)
  choose g hg using hi
  let E := ContinuousMap.sigmaCodHomeomorph (integralSimplex 0) Y
  let g' (s : S _⦋0⦌) : G :=
    let z := E ((TopCat.of (Σ i, Y i)).toSSetObjEquiv _ s)
    g z.1 (((TopCat.of (Y z.1)).toSSetObjEquiv _).symm z.2)
  have hg' (i : I) (s : Si i _⦋0⦌) : g' ((j i).app _ s) = g i s := by
    have he : ((TopCat.of (Σ i, Y i)).toSSetObjEquiv _ ((j i).app _ s)) =
        E.symm ⟨i, (TopCat.of (Y i)).toSSetObjEquiv _ s⟩ := rfl
    let v (z : Σ i, C(integralSimplex 0, Y i)) :=
      g z.1 (((TopCat.of (Y z.1)).toSSetObjEquiv _).symm z.2)
    change v (E _) = _
    rw [he, E.apply_symm_apply]
    exact congrArg (g i) (((TopCat.of (Y i)).toSSetObjEquiv _).symm_apply_apply s)
  refine ⟨g', ?_⟩
  intro s
  obtain ⟨i, t, ht⟩ := ((TopCat.of (Σ i, Y i)).toSSetObjEquiv _ s).exists_lift_sigma
  let si : Si i _⦋1⦌ := ((TopCat.of (Y i)).toSSetObjEquiv _).symm t
  have hs : s = (j i).app _ si := by
    apply ((TopCat.of (Σ i, Y i)).toSSetObjEquiv _).injective
    exact ht
  rw [hs]
  have hj (k : Fin 2) : S.δ k ((j i).app _ si) = (j i).app _ ((Si i).δ k si) :=
    (congrArg (fun h => h si) ((j i).naturality (SimplexCategory.δ k).op)).symm
  rw [hj, hj, hg', hg']
  exact hg i si

theorem sigma_h1_isZero {I : Type u} (Y : I → Type u)
    [∀ i, TopologicalSpace (Y i)] [∀ i, SimplyConnectedSpace (Y i)] :
    IsZero (ModTwoMayerVietoris.homology (Σ i, Y i) 1) := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of (Σ i, Y i))
  let R := ModTwoMayerVietoris.coefficient.{u}
  let C := S.chainComplex R
  let B := LinearMap.range (C.d 2 1).hom
  let Q := ModuleCat.of (ZMod 2) ((C.X 1) ⧸ B)
  let q : C.X 1 ⟶ Q := ModuleCat.ofHom B.mkQ
  have hq : C.d 2 1 ≫ q = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero B).mpr ⟨x, rfl⟩
  let f (s : S _⦋1⦌) : Q := q (S.ιChainComplex (R := R) s (ULift.up 1))
  have hf (s : S _⦋2⦌) :
      (∑ k : Fin 3, ((-1 : ℤ) ^ k.val) • f (S.δ k s)) = 0 := by
    let ev : (R ⟶ C.X 1) →+ Q :=
      { toFun := fun p => q (p (ULift.up 1))
        map_zero' := q.hom.map_zero
        map_add' := fun p r => q.hom.map_add _ _ }
    have h := congrArg ev (SSet.ιChainComplex_d S R s)
    have hz : ev (S.ιChainComplex s ≫ C.d 2 1) = 0 :=
      congrArg (fun p : C.X 2 ⟶ Q => p (S.ιChainComplex (R := R) s (ULift.up 1))) hq
    rw [hz, map_sum] at h
    have hh := h.symm
    simp only [map_zsmul] at hh
    exact hh
  obtain ⟨g, hg⟩ := sigma_one_cocycle_is_coboundary Y f hf
  let value (x : Q) : R ⟶ Q := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{u} (ZMod 2) ≃ₗ[ZMod 2] ZMod 2).toLinearMap.smulRight x)
  let psi : C.X 0 ⟶ Q := Sigma.desc (fun s : S _⦋0⦌ => value (g s))
  have hpsi (s : S _⦋0⦌) : psi (S.ιChainComplex (R := R) s (ULift.up 1)) = g s := by
    have h : S.ιChainComplex (R := R) s ≫ psi = value (g s) :=
      Sigma.ι_desc _ _
    have he := congrArg (fun p => p (ULift.up 1)) h
    change psi (S.ιChainComplex (R := R) s (ULift.up 1)) = (1 : ZMod 2) • g s at he
    simpa only [one_smul] using he
  have hedge (s : S _⦋1⦌) :
      (C.d 1 0 ≫ psi) (S.ιChainComplex (R := R) s (ULift.up 1)) = f s := by
    let ev : (R ⟶ C.X 0) →+ Q :=
      { toFun := fun p => psi (p (ULift.up 1))
        map_zero' := psi.hom.map_zero
        map_add' := fun p r => psi.hom.map_add _ _ }
    have h := congrArg ev (SSet.ιChainComplex_d S R s)
    rw [map_sum] at h
    change ev (S.ιChainComplex s ≫ C.d 1 0) = f s
    rw [h]
    simp only [map_zsmul]
    change (∑ k : Fin 2, ((-1 : ℤ) ^ k.val) • ev (S.ιChainComplex (S.δ k s))) = f s
    rw [Fin.sum_univ_two]
    norm_num only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
    rw [← sub_eq_add_neg]
    change psi (S.ιChainComplex (R := R) (S.δ 0 s) (ULift.up 1)) -
      psi (S.ιChainComplex (R := R) (S.δ 1 s) (ULift.up 1)) = f s
    rw [hpsi, hpsi]
    exact (hg s).symm
  have hfactor : C.d 1 0 ≫ psi = q := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ConcreteCategory.hom_ext
    intro a
    have ha : a = a.down • (ULift.up 1 : ULift.{u} (ZMod 2)) := by
      apply ULift.ext
      simp
    have he := hedge s
    change ((S.ιChainComplex s ≫ C.d 1 0 ≫ psi).hom) a =
      ((S.ιChainComplex s ≫ q).hom) a
    rw [ha, map_smul, map_smul]
    exact congrArg (a.down • ·) he
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  apply ShortComplex.exact_of_iso (C.isoSc' 2 1 0 (by simp) (by simp)).symm
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  change C.d 1 0 z = 0 at hz
  have hzero : q z = 0 := by
    rw [← hfactor]
    change psi (C.d 1 0 z) = 0
    rw [hz, map_zero]
  exact (Submodule.Quotient.mk_eq_zero B).mp hzero

end PoincareConjecture.M76.CollarOverlap
