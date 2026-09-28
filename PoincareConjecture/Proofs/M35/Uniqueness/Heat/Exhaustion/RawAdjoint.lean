import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TestAdjoint
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.RawTestOperator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointLowerOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

def rawTestAdjoint {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (f : Fin n → 𝓢(V, ℝ)) (j : Fin n) (x : V) : ℝ :=
  (∑ i, ∑ l, fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i l *
      fderiv ℝ (f j) y (e l)) x (e i)) -
    (∑ k, ∑ i, fderiv ℝ (fun y => rawFirstComponent D k j i y * f k y) x (e i)) +
    ∑ k, rawZeroComponent D k j x * f k x

private theorem cutoff_test_product {K : Set V} (η : V → ℝ)
    (hηK : ∀ x ∈ K, η x = 1) (a : V → ℝ) (f : supportedTests K) :
    (fun x => (η x * a x) * (f : 𝓢(V, ℝ)) x) =
      fun x => a x * (f : 𝓢(V, ℝ)) x := by
  funext x
  by_cases hx : x ∈ K
  · rw [hηK x hx, one_mul]
  · rw [f.property x hx, mul_zero, mul_zero]

theorem raw_lowerTestAdjoint_apply {K : Set V} (hK : IsClosed K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (f : supportedTests K) (k j : Fin n) (x : V) :
    (lowerTestAdjoint hK (rawCutoffFirstComponent D η hη k j)
      (rawCutoffZeroComponent D η hη k j) f : 𝓢(V, ℝ)) x =
      -(∑ i, fderiv ℝ (fun y => rawFirstComponent D k j i y *
        (f : 𝓢(V, ℝ)) y) x (e i)) + rawZeroComponent D k j x * (f : 𝓢(V, ℝ)) x := by
  have hzero := congrFun (cutoff_test_product η hηK (rawZeroComponent D k j) f) x
  have hfirst (i : Fin n) := cutoff_test_product η hηK (rawFirstComponent D k j i) f
  simp only [lowerTestAdjoint, Submodule.coe_add, Submodule.coe_neg, Submodule.coe_sum,
    add_apply, neg_apply, sum_apply]
  change -(∑ i, fderiv ℝ (fun y =>
    (η y * rawFirstComponent D k j i y) * (f : 𝓢(V, ℝ)) y) x (e i)) +
      (η x * rawZeroComponent D k j x) * (f : 𝓢(V, ℝ)) x = _
  simp only [hfirst, hzero]

theorem raw_vectorTestAdjoint_apply {K : Set V} (hK : IsClosed K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (f : Fin n → supportedTests K) (j : Fin n) (x : V) :
    (vectorTestAdjoint hK (rawCutoffPrincipalCoefficient g η hη)
      (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) f j : 𝓢(V, ℝ)) x =
        rawTestAdjoint D (fun k => (f k : 𝓢(V, ℝ))) j x := by
  simp only [vectorTestAdjoint, Submodule.coe_add, add_apply, Submodule.coe_sum, sum_apply]
  rw [raw_principalTestLaplacian_apply hK g η hη hηK]
  simp only [raw_lowerTestAdjoint_apply hK D η hη hηK,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, rawTestAdjoint]
  ring

theorem rawTestAdjoint_family_contDiffOn {J : Set ℝ} (F : RicciFlow n V J)
    (f : Fin n → 𝓢(V, ℝ)) (j : Fin n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × V => rawTestAdjoint (F.connection p.1) f j p.2)
      (J ×ˢ univ) := by
  unfold rawTestAdjoint
  apply ContDiffOn.add
  · apply ContDiffOn.sub
    · apply ContDiffOn.sum
      intro i _
      apply ContDiffOn.sum
      intro l _
      have hprod := (raw_inverseGram_entry_family_contDiffOn F i l).mul
        (((((f j).smooth'.fderiv_right (by simp)).clm_apply
          (contDiff_const (c := e l))).comp contDiff_snd).contDiffOn)
      exact (raw_family_spatial_fderiv_contDiffOn (f := fun t y =>
        (rawCoordinateGram (F.metric t) y)⁻¹ i l * fderiv ℝ (f j) y (e l))
          hprod).clm_apply (contDiffOn_const (c := e i))
    · apply ContDiffOn.sum
      intro k _
      apply ContDiffOn.sum
      intro i _
      have hprod := (rawFirstComponent_family_contDiffOn F k j i).mul
        ((f k).smooth'.comp contDiff_snd).contDiffOn
      exact (raw_family_spatial_fderiv_contDiffOn (f := fun t y =>
        rawFirstComponent (F.connection t) k j i y * f k y) hprod).clm_apply
          (contDiffOn_const (c := e i))
  · apply ContDiffOn.sum
    intro k _
    exact (rawZeroComponent_family_contDiffOn F k j).mul
      ((f k).smooth'.comp contDiff_snd).contDiffOn

end PoincareConjecture.M35.Uniqueness.Heat
