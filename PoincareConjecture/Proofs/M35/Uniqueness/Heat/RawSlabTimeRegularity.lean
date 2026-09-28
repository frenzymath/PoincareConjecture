import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SlabTimeRegularity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.RawSlab

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem contDiffAt_raw_compact_vector_heat {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1)
    {u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)}
    (hsol : PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U)
    {t : ℝ} (ht : t ∈ Ioo 0 (b - a)) : ContDiffAt ℝ ∞ U t := by
  obtain ⟨ell, hell, hEll⟩ := exists_raw_slab_cutoff_ellipticity (I := Icc a b)
    F isCompact_Icc hJ hK η hη hηK
  let A := fun r => rawCutoffPrincipalCoefficient (F.metric (a + r)) η hη
  let L := fun r => rawLowerFormOperator (F.connection (a + r)) hK.isClosed η hη
  have hshift : MapsTo (fun r : ℝ => a + r) (Icc 0 (b - a)) (Icc a b) := by
    intro r hr
    constructor <;> linarith only [hr.1, hr.2]
  have hAc : ContDiffOn ℝ ∞ (fun r => principalFormOperator K (A r)) (Icc 0 (b - a)) :=
    (contDiffOn_raw_principalFormOperator F hab hJ K η hη).comp
      (contDiffOn_const.add contDiffOn_id) hshift
  have hLc : ContDiffOn ℝ ∞ L (Icc 0 (b - a)) :=
    (contDiffOn_rawLowerFormOperator F hab hJ hK.isClosed η hη).comp
      (contDiffOn_const.add contDiffOn_id) hshift
  have hs : PrincipalValueHeat K A L 0 (b - a) u₀ v U := by
    simpa only [PrincipalValueHeat, A, L, zero_add] using hsol
  exact contDiffAt_principalValueHeat_slab hK A hell
    (fun r _ => rawCutoffPrincipalCoefficient_symmetric (F.metric (a + r)) η hη)
    (fun r hr => hEll (a + r) (hshift hr)) hAc L hLc hs ht

theorem exists_raw_compact_vector_heat_smooth_value {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) (hηK : ∀ x ∈ K, η x = 1)
    (u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)) :
    ∃ v U, PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U ∧
      ∀ t ∈ Ioo 0 (b - a), ContDiffAt ℝ ∞ U t := by
  obtain ⟨v, U, hsol⟩ := exists_raw_compact_vector_heat_on_slab F hab.le hJ hK η hη hη1 hηK u₀
  exact ⟨v, U, hsol, fun t ht => contDiffAt_raw_compact_vector_heat F hab hJ hK η hη hηK hsol ht⟩

end PoincareConjecture.M35.Uniqueness.Heat
