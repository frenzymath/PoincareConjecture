import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SecondTestHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoefficientTimeJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCompactHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem contDiffOn_one_of_successive_derivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → E)
    (hd : ∀ k t, t ∈ Icc a b → HasDerivWithinAt (f k) (f (k + 1) t) (Icc a b) t)
    (k : ℕ) : ContDiffOn ℝ 1 (f k) (Icc a b) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)]
  refine ⟨fun t ht => (hd k t ht).differentiableWithinAt, ?_⟩
  have hc : ContinuousOn (f (k + 1)) (Icc a b) :=
    fun t ht => (hd (k + 1) t ht).continuousWithinAt
  exact hc.congr (fun t ht => (hd k t ht).derivWithin ((uniqueDiffOn_Icc hab) t ht))

private theorem shifted_principal_derivative {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) (K : Set V)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 (b - a)) :
    HasDerivWithinAt
      (fun s => principalFormOperator K (rawPrincipalTimeJet F hab hJ η hη k (a + s)))
      (principalFormOperator K (rawPrincipalTimeJet F hab hJ η hη (k + 1) (a + t)))
      (Icc 0 (b - a)) t := by
  have hshift : MapsTo (fun t : ℝ => a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2]
  simpa only [one_smul, Function.comp_def] using!
    (hasDerivWithinAt_rawPrincipalFormTimeJet F hab hJ K η hη k (hshift ht)).scomp t
      ((hasDerivWithinAt_id t (Icc 0 (b - a))).const_add a) hshift

private theorem shifted_lower_derivative {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set V} (hK : IsClosed K)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc 0 (b - a)) :
    HasDerivWithinAt
      (fun s => dirichletVectorLowerOrder hK (rawFirstTimeJet F hab hJ η hη k (a + s))
        (rawZeroTimeJet F hab hJ η hη k (a + s)))
      (dirichletVectorLowerOrder hK (rawFirstTimeJet F hab hJ η hη (k + 1) (a + t))
        (rawZeroTimeJet F hab hJ η hη (k + 1) (a + t))) (Icc 0 (b - a)) t := by
  have hshift : MapsTo (fun t : ℝ => a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2]
  simpa only [one_smul, Function.comp_def] using!
    (hasDerivWithinAt_rawLowerFormTimeJet F hab hJ hK η hη k (hshift ht)).scomp t
      ((hasDerivWithinAt_id t (Icc 0 (b - a))).const_add a) hshift

private theorem raw_zero_jet_equation {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J) {K : Set V} (hK : IsClosed K)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (t : ℝ)
    (u w z : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (h : inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) w) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (dirichletVectorLowerOrder hK (rawFirstTimeJet F hab hJ η hη 0 t)
          (rawZeroTimeJet F hab hJ η hη 0 t) u) -
        principalVectorEnergy K (rawPrincipalTimeJet F hab hJ η hη 0 t) z u) :
    inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) w) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (rawLowerFormOperator (F.connection t) hK η hη u) -
        principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη) z u := by
  simpa only [rawPrincipalTimeJet_zero, rawFirstTimeJet_zero,
    rawZeroTimeJet_zero, rawLowerFormOperator] using h

private theorem exists_raw_jet_second_heat {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ a + τ < b ∧
      ∀ f : Fin n → supportedTests K,
      ∃ u w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
        u 0 = vectorTestForm K f ∧
        w 0 = vectorTestForm K (vectorTestGenerator hK.isClosed
          (rawPrincipalTimeJet F hab hJ η hη 0 (a + 0))
          (rawFirstTimeJet F hab hJ η hη 0 (a + 0))
          (rawZeroTimeJet F hab hJ η hη 0 (a + 0)) f) ∧
        ContinuousOn u (Icc 0 τ) ∧ ContinuousOn w (Icc 0 τ) ∧
        (∀ t ∈ Icc 0 τ, HasDerivWithinAt u (w t) (Icc 0 τ) t) ∧
        ∀ t ∈ Icc 0 τ, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (finiteHilbertMap (dirichletInclusion K) (w t)) =
              inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
                (dirichletVectorLowerOrder hK.isClosed
                  (rawFirstTimeJet F hab hJ η hη 0 (a + t))
                  (rawZeroTimeJet F hab hJ η hη 0 (a + t)) (u t)) -
                  principalVectorEnergy K
                    (rawPrincipalTimeJet F hab hJ η hη 0 (a + t)) z (u t) := by
  let A := fun k t => rawPrincipalTimeJet F hab hJ η hη k (a + t)
  let B := fun k t => rawFirstTimeJet F hab hJ η hη k (a + t)
  let C := fun k t => rawZeroTimeJet F hab hJ η hη k (a + t)
  let P := fun k t => principalFormOperator K (A k t)
  let L := fun k t => dirichletVectorLowerOrder hK.isClosed (B k t) (C k t)
  have hPd (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (b - a)) :
      HasDerivWithinAt (P k) (P (k + 1) t) (Icc 0 (b - a)) t :=
    shifted_principal_derivative F hab hJ K η hη k ht
  have hLd (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (b - a)) :
      HasDerivWithinAt (L k) (L (k + 1) t) (Icc 0 (b - a)) t :=
    shifted_lower_derivative F hab hJ hK.isClosed η hη k ht
  have hPc (k : ℕ) : ContDiffOn ℝ 1 (P k) (Icc 0 (b - a)) :=
    contDiffOn_one_of_successive_derivatives (sub_pos.mpr hab) P hPd k
  have hLc (k : ℕ) : ContDiffOn ℝ 1 (L k) (Icc 0 (b - a)) :=
    contDiffOn_one_of_successive_derivatives (sub_pos.mpr hab) L hLd k
  refine (exists_rawCutoffPrincipalCoefficient_ellipticity
    (F.metric a) hK η hη hηK).elim ?_
  intro ell he
  have hell : 0 < ell := he.1
  have hEll := he.2
  have hA0 : A 0 0 = rawCutoffPrincipalCoefficient (F.metric a) η hη := by
    simp only [A, add_zero, rawPrincipalTimeJet_zero]
  have hsymm : ∀ i j x, A 0 0 i j x = A 0 0 j i x := by
    rw [hA0]
    exact rawCutoffPrincipalCoefficient_symmetric (F.metric a) η hη
  have hell0 : ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A 0 0 i j x * ξ i * ξ j := by
    rw [hA0]
    exact hEll
  refine (exists_principal_second_test_heat hK
    (A 0) (A 1) (A 2) (B 0) (B 1) (B 2) (C 0) (C 1) (C 2)
    hell (sub_pos.mpr hab) hsymm hell0 (hPc 0) (hPc 1) (hPc 2).continuousOn
    (fun t ht => (hPd 0 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => (hPd 1 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (hLc 0) (hLc 1) (hLc 2).continuousOn
    (fun t ht => (hLd 0 t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => (hLd 1 t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))).elim ?_
  intro τ hτ
  exact ⟨τ, hτ.1, hτ.2.1, by linarith only [hτ.2.2.1], hτ.2.2.2⟩

theorem exists_raw_second_compact_vector_heat {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ a + τ < b ∧
      ∀ f : Fin n → supportedTests K,
      ∃ u w : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K),
        u 0 = vectorTestForm K f ∧
        w 0 = vectorTestForm K (vectorTestGenerator hK.isClosed
          (rawCutoffPrincipalCoefficient (F.metric a) η hη)
          (rawCutoffFirstComponent (F.connection a) η hη)
          (rawCutoffZeroComponent (F.connection a) η hη) f) ∧
        ContinuousOn u (Icc 0 τ) ∧ ContinuousOn w (Icc 0 τ) ∧
        (∀ t ∈ Icc 0 τ, HasDerivWithinAt u (w t) (Icc 0 τ) t) ∧
        ∀ t ∈ Icc 0 τ, ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (finiteHilbertMap (dirichletInclusion K) (w t)) =
              inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
                (rawLowerFormOperator (F.connection (a + t)) hK.isClosed η hη (u t)) -
                  principalVectorEnergy K
                    (rawCutoffPrincipalCoefficient (F.metric (a + t)) η hη) z (u t) := by
  refine (exists_raw_jet_second_heat F hab hJ hK η hη hηK).elim ?_
  intro τ hτ
  refine ⟨τ, hτ.1, hτ.2.1, hτ.2.2.1, ?_⟩
  intro f
  refine (hτ.2.2.2 f).elim ?_
  intro u hu
  refine hu.elim ?_
  intro w hw
  refine ⟨u, w, hw.1, ?_, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, ?_⟩
  · simpa only [rawPrincipalTimeJet_zero, rawFirstTimeJet_zero,
      rawZeroTimeJet_zero, add_zero] using hw.2.1
  · intro t ht z
    exact raw_zero_jet_equation F hab hJ hK.isClosed η hη (a + t) (u t) (w t) z
      (hw.2.2.2.2.2 t ht z)

end PoincareConjecture.M35.Uniqueness.Heat
