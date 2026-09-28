import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralMayerVietoris








set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped BigOperators

universe u v

namespace Poincare.Topology

attribute [local instance 2000] Submodule.Quotient.module

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def integralSimplexHomeomorphEquiv (e : X ≃ₜ Y) (n : Nat) :
    C(integralSimplex n, X) ≃ C(integralSimplex n, Y) where
  toFun s := (e : C(X, Y)).comp s
  invFun s := (e.symm : C(Y, X)).comp s
  left_inv s := by ext z; exact e.symm_apply_apply (s z)
  right_inv s := by ext z; exact e.apply_symm_apply (s z)

def integralCoefficientUniverseEquiv : ULift.{u} Int ≃ₗ[Int] ULift.{v} Int :=
  ULift.moduleEquiv.trans ULift.moduleEquiv.symm

def integralChainHomeomorphEquiv (e : X ≃ₜ Y) (n : Nat) :
    (integralChains X).X n ≃ₗ[Int] (integralChains Y).X n :=
  (integralChainCoordinates X n).trans
    ((Finsupp.lcongr (integralSimplexHomeomorphEquiv e n)
      integralCoefficientUniverseEquiv).trans (integralChainCoordinates Y n).symm)

@[simp]
theorem integralChainHomeomorphEquiv_generator (e : X ≃ₜ Y) {n : Nat}
    (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
    integralChainHomeomorphEquiv e n (integralSingularGenerator s a) =
      integralSingularGenerator ((e : C(X, Y)).comp s) (ULift.up a.down) := by
  apply (integralChainCoordinates Y n).injective
  change integralChainCoordinates Y n ((integralChainCoordinates Y n).symm
      (Finsupp.lcongr (integralSimplexHomeomorphEquiv e n)
        integralCoefficientUniverseEquiv
          (integralChainCoordinates X n (integralSingularGenerator s a)))) = _
  rw [LinearEquiv.apply_symm_apply, integralChainCoordinates_generator,
    Finsupp.lcongr_single, integralChainCoordinates_generator]
  rfl

theorem integralChainHomeomorphEquiv_coordinates (e : X ≃ₜ Y) (n : Nat)
    (c : (integralChains X).X n) (s : C(integralSimplex n, Y)) :
    integralChainCoordinates Y n (integralChainHomeomorphEquiv e n c) s =
      ULift.up ((integralChainCoordinates X n c
        ((e.symm : C(Y, X)).comp s)).down) := by
  simp [integralChainHomeomorphEquiv, Finsupp.lcongr_apply_apply,
    integralSimplexHomeomorphEquiv, integralCoefficientUniverseEquiv]

theorem integralChainHomeomorphEquiv_boundary (e : X ≃ₜ Y) (n : Nat)
    (c : (integralChains X).X (n + 1)) :
    integralChainHomeomorphEquiv e n ((integralChains X).d (n + 1) n c) =
      (integralChains Y).d (n + 1) n (integralChainHomeomorphEquiv e (n + 1) c) := by
  have hgen (s : C(integralSimplex (n + 1), X)) (a : ULift.{u} Int) :
      integralChainHomeomorphEquiv e n
          ((integralChains X).d (n + 1) n (integralSingularGenerator s a)) =
        (integralChains Y).d (n + 1) n
          (integralChainHomeomorphEquiv e (n + 1) (integralSingularGenerator s a)) := by
    have hx := congrArg (fun f => f.hom a) (integralSingularGenerator_boundary s)
    have hy := congrArg (fun f => f.hom (ULift.up a.down))
      (integralSingularGenerator_boundary ((e : C(X, Y)).comp s))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_zsmul] at hx hy
    rw [hx, integralChainHomeomorphEquiv_generator, hy]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change integralChainHomeomorphEquiv e n
        (((-1 : Int) ^ i.val) • integralSingularGenerator (s.comp (integralSimplexFace n i)) a) =
      ((-1 : Int) ^ i.val) • integralSingularGenerator
        (((e : C(X, Y)).comp s).comp (integralSimplexFace n i)) (ULift.up a.down)
    rw [map_zsmul, integralChainHomeomorphEquiv_generator]
    rfl
  rw [integral_chain_finite_representation (n + 1) c]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact hgen s _

theorem integralChainHomeomorphEquiv_d (e : X ≃ₜ Y) (i j : Nat)
    (c : (integralChains X).X i) :
    integralChainHomeomorphEquiv e j ((integralChains X).d i j c) =
      (integralChains Y).d i j (integralChainHomeomorphEquiv e i c) := by
  by_cases h : j + 1 = i
  · subst i
    exact integralChainHomeomorphEquiv_boundary e j c
  · rw [(integralChains X).shape i j h, (integralChains Y).shape i j h]
    simp

theorem integralChainHomeomorphEquiv_subspace_iff (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : Nat)
    (c : (integralChains X).X n) :
    integralChainHomeomorphEquiv e n c ∈
        LinearMap.range ((integralSubspaceChains B).f n).hom ↔
      c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom := by
  rw [integral_subspace_range_iff, integral_subspace_range_iff]
  constructor
  · intro hc s hs x hx
    obtain ⟨z, rfl⟩ := hx
    apply (h (s z)).mpr
    apply hc ((e : C(X, Y)).comp s) ?_ ⟨z, rfl⟩
    rw [Finsupp.mem_support_iff, integralChainHomeomorphEquiv_coordinates]
    have he : (e.symm : C(Y, X)).comp ((e : C(X, Y)).comp s) = s := by
      ext z
      exact e.symm_apply_apply (s z)
    rw [he]
    intro hz
    apply Finsupp.mem_support_iff.mp hs
    apply ULift.ext
    exact congrArg (fun z : ULift.{v} Int => z.down) hz
  · intro hc s hs y hy
    obtain ⟨z, rfl⟩ := hy
    have hm : ((e.symm : C(Y, X)).comp s) ∈ (integralChainCoordinates X n c).support := by
      rw [Finsupp.mem_support_iff]
      intro hz
      rw [Finsupp.mem_support_iff, integralChainHomeomorphEquiv_coordinates, hz] at hs
      exact hs rfl
    have hx := (h (e.symm (s z))).mp (hc _ hm ⟨z, rfl⟩)
    simpa only [e.apply_symm_apply] using hx

theorem integralChainHomeomorphEquiv_subspace (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : Nat) :
    (LinearMap.range ((integralSubspaceChains A).f n).hom).map
        (integralChainHomeomorphEquiv e n).toLinearMap =
      LinearMap.range ((integralSubspaceChains B).f n).hom := by
  ext c
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (integralChainHomeomorphEquiv_subspace_iff e A B h n a).mpr ha
  · intro hc
    obtain ⟨a, rfl⟩ := (integralChainHomeomorphEquiv e n).surjective c
    exact ⟨a, (integralChainHomeomorphEquiv_subspace_iff e A B h n a).mp hc, rfl⟩

def integralRelativeQuotientEquiv (A : Set X) (n : Nat) :
    (integralRelativeChains A).X n ≃ₗ[Int]
      ((integralChains X).X n ⧸ LinearMap.range ((integralSubspaceChains A).f n).hom) :=
  (((integralRelativeProjection A).f n).hom.quotKerEquivOfSurjective
    (integralProjection_surjective (integralSubspaceChains A) n)).symm.trans
      (Submodule.quotEquivOfEq
        (LinearMap.ker ((integralRelativeProjection A).f n).hom)
        (LinearMap.range ((integralSubspaceChains A).f n).hom) (by
          apply Submodule.ext
          intro c
          exact integralProjection_eq_zero_iff (integralSubspaceChains A) n c))

@[simp]
theorem integralRelativeQuotientEquiv_projection (A : Set X) (n : Nat)
    (c : (integralChains X).X n) :
    integralRelativeQuotientEquiv A n ((integralRelativeProjection A).f n c) =
      (LinearMap.range ((integralSubspaceChains A).f n).hom).mkQ c := by
  simp [integralRelativeQuotientEquiv]

def integralRelativeHomeomorphEquiv (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : Nat) :
    (integralRelativeChains A).X n ≃ₗ[Int] (integralRelativeChains B).X n :=
  (integralRelativeQuotientEquiv A n).trans
    ((Submodule.Quotient.equiv _ _ (integralChainHomeomorphEquiv e n)
      (integralChainHomeomorphEquiv_subspace e A B h n)).trans
        (integralRelativeQuotientEquiv B n).symm)

@[simp]
theorem integralRelativeHomeomorphEquiv_projection (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) (n : Nat)
    (c : (integralChains X).X n) :
    integralRelativeHomeomorphEquiv e A B h n ((integralRelativeProjection A).f n c) =
      (integralRelativeProjection B).f n (integralChainHomeomorphEquiv e n c) := by
  apply (integralRelativeQuotientEquiv B n).injective
  simp [integralRelativeHomeomorphEquiv]

theorem integralRelativeHomeomorphEquiv_d (e : X ≃ₜ Y)
    (A : Set X) (B : Set Y) (h : ∀ x, x ∈ A ↔ e x ∈ B) (i j : Nat)
    (c : (integralRelativeChains A).X i) :
    integralRelativeHomeomorphEquiv e A B h j ((integralRelativeChains A).d i j c) =
      (integralRelativeChains B).d i j (integralRelativeHomeomorphEquiv e A B h i c) := by
  obtain ⟨a, rfl⟩ := integralProjection_surjective (integralSubspaceChains A) i c
  have hA := congrArg (fun f => f a) ((integralRelativeProjection A).comm i j)
  have hB := congrArg (fun f => f (integralChainHomeomorphEquiv e i a))
    ((integralRelativeProjection B).comm i j)
  change (integralRelativeChains A).d i j ((integralRelativeProjection A).f i a) =
    (integralRelativeProjection A).f j ((integralChains X).d i j a) at hA
  change (integralRelativeChains B).d i j ((integralRelativeProjection B).f i
      (integralChainHomeomorphEquiv e i a)) =
    (integralRelativeProjection B).f j ((integralChains Y).d i j
      (integralChainHomeomorphEquiv e i a)) at hB
  rw [hA, integralRelativeHomeomorphEquiv_projection,
    integralRelativeHomeomorphEquiv_projection, hB, integralChainHomeomorphEquiv_d]

theorem integralRelativeHomeomorphEquiv_naturality (e : X ≃ₜ Y)
    {A A' : Set X} {B B' : Set Y}
    (h : ∀ x, x ∈ A ↔ e x ∈ B) (h' : ∀ x, x ∈ A' ↔ e x ∈ B')
    (hA : A ⊆ A') (hB : B ⊆ B') (n : Nat) (c : (integralRelativeChains A).X n) :
    (integralRelativeRestriction hB).f n (integralRelativeHomeomorphEquiv e A B h n c) =
      integralRelativeHomeomorphEquiv e A' B' h' n ((integralRelativeRestriction hA).f n c) := by
  obtain ⟨a, rfl⟩ := integralProjection_surjective (integralSubspaceChains A) n c
  have hPA := congrArg (fun f => f.f n a) (integralRelativeRestriction_projection hA)
  have hPB := congrArg (fun f => f.f n (integralChainHomeomorphEquiv e n a))
    (integralRelativeRestriction_projection hB)
  change (integralRelativeRestriction hA).f n ((integralRelativeProjection A).f n a) =
    (integralRelativeProjection A').f n a at hPA
  change (integralRelativeRestriction hB).f n ((integralRelativeProjection B).f n
      (integralChainHomeomorphEquiv e n a)) =
    (integralRelativeProjection B').f n (integralChainHomeomorphEquiv e n a) at hPB
  rw [integralRelativeHomeomorphEquiv_projection, hPB, hPA,
    integralRelativeHomeomorphEquiv_projection]

end Poincare.Topology
