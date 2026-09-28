import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.GroupTheory.SpecificGroups.Dihedral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture

theorem PuncturedProjectiveSphere.pathConnectedSpace (p : RealProjectiveThree) :
    PathConnectedSpace (PuncturedProjectiveSphere p) := by
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective p
  have he : {q : UnitThreeSphere | Quotient.mk' q ≠ Quotient.mk' a} = {a, -a}ᶜ := by
    ext q
    simp only [mem_ofPred_eq, mem_compl_iff, mem_insert_iff, mem_singleton_iff]
    exact not_congr Quotient.eq
  change PathConnectedSpace {q : UnitThreeSphere | Quotient.mk' q ≠ Quotient.mk' a}
  rw [he]
  obtain ⟨e⟩ := Poincare.Topology.sphereComplementTwoPointsHomeomorphPuncturedEuclidean
    (n := 2) a
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  let : PathConnectedSpace ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank 0)
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

private def twoPointReflectionHom {A : Type*} (x y : A) (hxy : x ≠ y)
    (hpair : ∀ z : A, z = x ∨ z = y) (k : ZMod 0) :
    Equiv.Perm A →* DihedralGroup 0 := by
  classical
  have hfix (σ : Equiv.Perm A) (hσ : σ x = x) : σ y = y := by
    apply (hpair (σ y)).resolve_left
    intro hy
    exact hxy (σ.injective (hσ.trans hy.symm))
  have hswap (σ : Equiv.Perm A) (hσ : σ x ≠ x) : σ x = y ∧ σ y = x := by
    have hx := (hpair (σ x)).resolve_left hσ
    refine ⟨hx, (hpair (σ y)).resolve_right ?_⟩
    intro hy
    exact hxy (σ.injective (hx.trans hy.symm))
  refine {
    toFun := fun σ => if σ x = x then 1 else DihedralGroup.sr k
    map_one' := by simp
    map_mul' := ?_ }
  intro σ τ
  by_cases hσ : σ x = x
  · by_cases hτ : τ x = x
    · have hστ : (σ * τ) x = x := by rw [Equiv.Perm.mul_apply, hτ, hσ]
      simp only [if_pos hστ, if_pos hσ, if_pos hτ, one_mul]
    · have hστ : (σ * τ) x ≠ x := by
        rw [Equiv.Perm.mul_apply, (hswap τ hτ).1, hfix σ hσ]
        exact hxy.symm
      simp only [if_neg hστ, if_pos hσ, if_neg hτ, one_mul]
  · by_cases hτ : τ x = x
    · have hστ : (σ * τ) x ≠ x := by rwa [Equiv.Perm.mul_apply, hτ]
      simp only [if_neg hστ, if_neg hσ, if_pos hτ, mul_one]
    · have hστ : (σ * τ) x = x := by
        rw [Equiv.Perm.mul_apply, (hswap τ hτ).1, (hswap σ hσ).2]
      simp only [if_pos hστ, if_neg hσ, if_neg hτ,
        DihedralGroup.sr_mul_sr, sub_self, DihedralGroup.r_zero]

namespace StandardPuncturedProjectiveCover

variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}

theorem exists_dihedral_reflection_monodromy
    (S : StandardPuncturedProjectiveCover Q p U) (b : U) (k : ZMod 0) :
    ∃ f : FundamentalGroup U b →* DihedralGroup 0, DihedralGroup.sr k ∈ f.range := by
  classical
  let : PathConnectedSpace (PuncturedProjectiveSphere p) :=
    PuncturedProjectiveSphere.pathConnectedSpace p
  obtain ⟨a, rfl⟩ := S.restrictedCover_surjective b
  let cov := S.restrictedCover_isCoveringMap
  let x : S.restrictedCover ⁻¹' {S.restrictedCover a} := ⟨a, rfl⟩
  have hy : S.restrictedCover (PuncturedProjectiveSphere.antipode a) =
      S.restrictedCover a := (S.restrictedCover_eq_iff _ _).mpr (Or.inr rfl)
  let y : S.restrictedCover ⁻¹' {S.restrictedCover a} :=
    ⟨PuncturedProjectiveSphere.antipode a, hy⟩
  have hxy : x ≠ y := by
    intro h
    exact PuncturedProjectiveSphere.ne_antipode a (congrArg Subtype.val h)
  have hpair (z : S.restrictedCover ⁻¹' {S.restrictedCover a}) : z = x ∨ z = y := by
    rcases (S.restrictedCover_eq_iff z.val a).mp z.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  let φ := twoPointReflectionHom x y hxy hpair k
  let Γ : Path.Homotopic.Quotient a (PuncturedProjectiveSphere.antipode a) :=
    .mk (PathConnectedSpace.somePath _ _)
  let γ : FundamentalGroup U (S.restrictedCover a) :=
    (Γ.map ⟨S.restrictedCover, cov.continuous⟩).cast rfl hy.symm
  have hγ : cov.monodromy γ x = y := by
    apply cov.monodromy_eq_of_map_eq Γ
    simp [γ, x, y]
  refine ⟨φ.comp (cov.monodromyPerm (S.restrictedCover a)), ⟨γ, ?_⟩⟩
  simp [MonoidHom.comp_apply, φ, twoPointReflectionHom,
    IsCoveringMap.coe_monodromyPerm, hγ, hxy.symm]

end StandardPuncturedProjectiveCover

end PoincareConjecture
