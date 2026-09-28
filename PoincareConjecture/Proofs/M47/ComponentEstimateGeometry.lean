import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}



theorem six_mul_lt_scalar_of_sectional_lower (D : LeviCivitaData g)
    (x : M) (k : ℝ)
    (hsec : ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x v w → k < D.sectionalCurvature x v w) :
    6 * k < D.scalarCurvature x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 3) x)
  have hdim : d = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  have hinner (i j : Fin d) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hstrict (i j : Fin d) (hij : i ≠ j) :
      k < D.curvatureTensor x (b i) (b j) (b i) (b j) := by
    have horth : LeviCivitaData.IsOrthonormalPair g x (b i) (b j) := by
      simp [LeviCivitaData.IsOrthonormalPair, hinner, hij]
    have h := hsec (b i) (b j) horth
    simpa only [LeviCivitaData.sectionalCurvature, horth.1, horth.2.1,
      horth.2.2, mul_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using h
  have hle (i j : Fin d) :
      (if i = j then 0 else k) ≤ D.curvatureTensor x (b i) (b j) (b i) (b j) := by
    by_cases hij : i = j
    · subst j
      simp [LeviCivitaData.curvatureTensor, M04.curvature_self]
    · simpa only [if_neg hij] using (hstrict i j hij).le
  have hsum : (∑ i : Fin d, ∑ j : Fin d, if i = j then 0 else k) = 6 * k := by
    calc
      _ = ∑ i : Fin d, ∑ j : Fin d, (k - if i = j then k else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by
        simp [Finset.sum_sub_distrib, hdim]
        ring
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  rw [← hsum]
  exact Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum (fun c _ => hle a c))
    ⟨i, Finset.mem_univ i, Finset.sum_lt_sum (fun c _ => hle i c)
      ⟨j, Finset.mem_univ j, by simpa only [if_neg hij] using hstrict i j hij⟩⟩



theorem component_scalar_pos {C : ℝ} (N : SingularCComponent g D C)
    {x : M} (hx : x ∈ N.carrier) : 0 < D.scalarCurvature x := by
  simpa only [mul_zero] using
    six_mul_lt_scalar_of_sectional_lower D x 0 (N.positive_sectional x hx)



theorem component_scalar_le_sup {C : ℝ} (N : SingularCComponent g D C)
    {x : M} (hx : x ∈ N.carrier) :
    D.scalarCurvature x ≤ scalarCurvatureSupOn g D N.carrier := by
  have hb : BddAbove (range (fun y : N.carrier => D.scalarCurvature y.1)) := by
    apply (N.compact.bddAbove_image
      (M34.contMDiff_scalarCurvature D).continuous.continuousOn).mono
    rintro _ ⟨y, rfl⟩
    exact mem_image_of_mem _ y.2
  exact le_csSup hb (mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)



theorem component_scalar_ratio {C : ℝ} (N : SingularCComponent g D C)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    D.scalarCurvature y < (C / 6) * D.scalarCurvature x := by
  have htrace := six_mul_lt_scalar_of_sectional_lower D x
    (C⁻¹ * scalarCurvatureSupOn g D N.carrier) (N.sectional_lower x hx)
  have hscaled := mul_lt_mul_of_pos_left htrace N.constant_pos
  have hcancel : C * (6 * (C⁻¹ * scalarCurvatureSupOn g D N.carrier)) =
      6 * scalarCurvatureSupOn g D N.carrier := by
    field_simp [N.constant_pos.ne']
  rw [hcancel] at hscaled
  have hybound := component_scalar_le_sup N hy
  nlinarith



theorem twoComponent_scalar_bound {C Q : ℝ}
    (N : SingularCComponent g D (2 * C)) {x : M}
    (hx : x ∈ N.carrier) (hQ : D.scalarCurvature x = Q)
    {y : M} (hy : y ∈ N.carrier) : D.scalarCurvature y < (C / 3) * Q := by
  have h := component_scalar_ratio N hx hy
  rw [hQ] at h
  convert h using 1
  ring



theorem component_diameter_lt {C : ℝ} (N : SingularCComponent g D C)
    {x : M} (hx : x ∈ N.carrier) :
    intrinsicDiameter g N.carrier <
      ENNReal.ofReal (C * D.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  have hb : BddBelow (range (fun y : N.carrier =>
      D.scalarCurvature y.1 ^ (-1 / 2 : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact Real.rpow_nonneg (component_scalar_pos N y.2).le _
  have hi := csInf_le hb (mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
  exact N.diameter_upper.trans_le (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hi N.constant_pos.le))



theorem component_subset_ball {C : ℝ} (N : SingularCComponent g D C)
    {x : M} (hx : x ∈ N.carrier) :
    N.carrier ⊆ g.ball x (C * D.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  intro y hy
  exact ((edist_le_intrinsicEDist N.carrier x y).trans
    (intrinsicEDist_le_intrinsicDiameter hx hy)).trans_lt (component_diameter_lt N hx)

end PoincareConjecture.M47
