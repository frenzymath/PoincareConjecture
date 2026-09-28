import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.NormBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Reaction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.SlabBounds
import PoincareConjecture.Proofs.Horizon.Analysis.Asymptotics.Harnack
import Mathlib.Analysis.Calculus.Deriv.MeanValue














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem abs_scalarCurvature_le_curvatureTensorNorm
    (D : LeviCivitaData g) (x : M) :
    |D.scalarCurvature x| ≤ (n : ℝ) ^ 2 * D.curvatureTensorNorm x := by
  let b := g.orthonormalBasis x
  let R := fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hcomp (i j k l) : |R i j k l| ≤ D.curvatureTensorNorm x := by
    apply Real.abs_le_sqrt
    change (R i j k l) ^ 2 ≤ ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l) ^ 2
    calc
      (R i j k l) ^ 2 ≤ ∑ l, (R i j k l) ^ 2 :=
        Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      _ ≤ ∑ k, ∑ l, (R i j k l) ^ 2 :=
        Finset.single_le_sum (f := fun k => ∑ l, (R i j k l) ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ k)
      _ ≤ ∑ j, ∑ k, ∑ l, (R i j k l) ^ 2 :=
        Finset.single_le_sum (f := fun j => ∑ k, ∑ l, (R i j k l) ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, (R i j k l) ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ∑ k, ∑ l, (R i j k l) ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ i)
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
    finrank_euclideanSpace_fin
  change |∑ i, ∑ j, R i j i j| ≤ _
  calc
    _ ≤ ∑ i, |∑ j, R i j i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |R i j i j| := Finset.sum_le_sum (fun _ _ =>
      Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          D.curvatureTensorNorm x := Finset.sum_le_sum (fun i _ =>
            Finset.sum_le_sum (fun j _ => hcomp i j i j))
    _ = _ := by simp [hdim, pow_two, mul_assoc]

set_option maxHeartbeats 800000 in


theorem curvatureOperatorBound_scalarCurvature
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hoperator : D.NonnegativeCurvatureOperator x) :
    0 ≤ D.scalarCurvature x ∧ CurvatureOperatorBound D (D.scalarCurvature x) x := by
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let R := fun i j k l : I => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hsym := hD.2.2.2.1
  have hlast : ∀ i j k l, R i j k l = -R i j l k :=
    fun i j k l => (hsym x (b i) (b j) (b k) (b l)).1
  have hpair : ∀ i j k l, R i j k l = R k l i j :=
    fun i j k l => (hsym x (b i) (b j) (b k) (b l)).2.1
  have hfirst : ∀ i j k l, R i j k l = -R j i k l := by
    intro i j k l
    rw [hpair i j k l, hlast k l i j, hpair k l j i]
  have hquad (U : I → I → ℝ) :
      0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * U i j * U k l := by
    have h := hoperator (fun i j => (U i j - U j i) / 2) (by
      unfold IsSkewCoefficient
      intros
      ring)
    have heq := Poincare.RicciFlow.Harnack.hamiltonBlock_antisymmetrize R
      (fun _ _ _ => 0) (fun _ _ => 0) U (fun _ => 0)
      hfirst hlast (by intros; simp)
    simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add] at heq
    rw [← heq]
    simpa only [curvatureOperatorQuadratic, R, b, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hpairquad (v : I × I → ℝ) :
      0 ≤ ∑ p, ∑ q, R p.1 p.2 q.1 q.2 * v p * v q := by
    simpa only [Fintype.sum_prod_type] using hquad (fun i j => v (i, j))
  have htrace : (∑ p : I × I, R p.1 p.2 p.1 p.2) = D.scalarCurvature x := by
    simp only [Fintype.sum_prod_type]
    rfl
  have hdiag (p : I × I) : 0 ≤ R p.1 p.2 p.1 p.2 := by
    have h := hpairquad (Pi.single p 1)
    simpa only [Pi.single_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h
  refine ⟨htrace ▸ Finset.sum_nonneg (fun p _ => hdiag p), ?_⟩
  intro U hU
  have hbound := Poincare.LinearAlgebra.quadratic_le_trace_mul_sum_sq
    (fun p q : I × I => R p.1 p.2 q.1 q.2) hpairquad
    (fun p => U p.1 p.2)
  rw [htrace] at hbound
  rw [abs_of_nonneg (hoperator U hU)]
  simpa only [Fintype.sum_prod_type, curvatureOperatorQuadratic, R, b,
    mul_comm, mul_left_comm, mul_assoc] using hbound



theorem curvatureTensorNorm_le_scalarCurvature
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hoperator : D.NonnegativeCurvatureOperator x) :
    D.curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * D.scalarCurvature x := by
  obtain ⟨hscalar, hbound⟩ := D.curvatureOperatorBound_scalarCurvature hD x hoperator
  exact D.curvatureTensorNorm_le_of_operator_bound x _ hscalar hbound hD

end PoincareConjecture.LeviCivitaData

namespace Poincare.RicciFlow.Harnack





theorem exists_uniform_bound_of_local_right_bound_and_harnack
    {X : Type*} (f : X → ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hcontinuous : ∀ x, ContinuousOn (f x) (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x, 0 ≤ f x t)
    (hslice : ∀ t ∈ Icc a b, ∃ K : ℝ, ∀ x, f x t ≤ K)
    (hright : ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
      ∀ t ∈ Icc c d, ∀ x, f x t ≤ K)
    (harnack : ∀ c ∈ Ioc a b,
      (∃ K : ℝ, ∀ t ∈ Icc a c, ∀ x, f x t ≤ K) →
      ∀ x, MonotoneOn (fun t => (t - a) * f x t) (Icc a c)) :
    ∃ K : ℝ, ∀ t ∈ Icc a b, ∀ x, f x t ≤ K := by
  obtain ⟨c₀, hc₀, K₀, hK₀⟩ := hright a ⟨le_rfl, hab⟩
  let S : Set ℝ := {c | c ∈ Icc a b ∧
    ∃ K : ℝ, ∀ t ∈ Icc a c, ∀ x, f x t ≤ K}
  have hc₀S : c₀ ∈ S := ⟨⟨hc₀.1.le, hc₀.2⟩, K₀, hK₀⟩
  have hSne : S.Nonempty := ⟨c₀, hc₀S⟩
  have hSbdd : BddAbove S := ⟨b, fun c hc => hc.1.2⟩
  let bstar := sSup S
  have hc₀star : c₀ ≤ bstar := le_csSup hSbdd hc₀S
  have hastar : a < bstar := hc₀.1.trans_le hc₀star
  have hstarb : bstar ≤ b := csSup_le hSne (fun c hc => hc.1.2)
  have hterminal (x : X) {t : ℝ} (ht : t ∈ Ioc a bstar) :
      (t - a) * f x t ≤ (bstar - a) * f x bstar := by
    rcases ht.2.eq_or_lt with rfl | htb
    · exact le_rfl
    apply Poincare.Asymptotics.le_at_right_endpoint htb continuousWithinAt_const
      (((continuousOn_id.sub continuousOn_const).mul
        ((hcontinuous x).mono (Icc_subset_Icc ht.1.le hstarb))) bstar
          ⟨htb.le, le_rfl⟩)
    intro s hs
    obtain ⟨c, hcS, hsc⟩ := (lt_csSup_iff hSbdd hSne).mp hs.2
    exact harnack c ⟨ht.1.trans (hs.1.trans hsc), hcS.1.2⟩ hcS.2 x
      ⟨ht.1.le, hs.1.le.trans hsc.le⟩ ⟨ht.1.le.trans hs.1.le, hsc.le⟩ hs.1.le
  obtain ⟨Kstar, hKstar⟩ := hslice bstar ⟨hastar.le, hstarb⟩
  have hfull : ∃ K : ℝ, ∀ t ∈ Icc a bstar, ∀ x, f x t ≤ K := by
    refine ⟨max K₀ ((bstar - a) * Kstar / (c₀ - a)), ?_⟩
    intro t ht x
    rcases le_total t c₀ with htc₀ | hc₀t
    · exact (hK₀ t ⟨ht.1, htc₀⟩ x).trans (le_max_left _ _)
    · apply le_trans _ (le_max_right _ _)
      apply (le_div_iff₀ (sub_pos.mpr hc₀.1)).mpr
      have hweight := mul_le_mul_of_nonneg_right (sub_le_sub_right hc₀t a)
        (hnonneg t ⟨ht.1, ht.2.trans hstarb⟩ x)
      have hmono := hterminal x ⟨hc₀.1.trans_le hc₀t, ht.2⟩
      have htop := mul_le_mul_of_nonneg_left (hKstar x) (sub_nonneg.mpr hastar.le)
      nlinarith
  have hstarS : bstar ∈ S := ⟨⟨hastar.le, hstarb⟩, hfull⟩
  have hstar_eq : bstar = b := by
    apply le_antisymm hstarb
    by_contra hnot
    have hlt : bstar < b := lt_of_not_ge hnot
    obtain ⟨d, hd, Kright, hKright⟩ := hright bstar ⟨hastar.le, hlt⟩
    obtain ⟨Kleft, hKleft⟩ := hfull
    have hdS : d ∈ S := by
      refine ⟨⟨hastar.le.trans hd.1.le, hd.2⟩, max Kleft Kright, ?_⟩
      intro t ht x
      rcases le_total t bstar with hleft | hright
      · exact (hKleft t ⟨ht.1, hleft⟩ x).trans (le_max_left _ _)
      · exact (hKright t ⟨hright, ht.2⟩ x).trans (le_max_right _ _)
    exact (not_lt_of_ge (le_csSup hSbdd hdS)) hd.1
  simpa only [hstar_eq] using hfull

end Poincare.RicciFlow.Harnack

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem monotoneOn_time_mul_scalarCurvature_of_harnack
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a b : ℝ} (hJ : Icc a b ⊆ J) (x : M)
    (harnack : ∀ t ∈ Ioo a b,
      0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x +
        (F.connection t).scalarCurvature x / (t - a)) :
    MonotoneOn (fun t => (t - a) * (F.connection t).scalarCurvature x) (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (f := fun t => (t - a) * (F.connection t).scalarCurvature x)
    ((continuousOn_id.sub continuousOn_const).mul
      ((Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time hC J F x).mono hJ))
    (f' := fun t => (F.connection t).scalarCurvature x + (t - a) *
      ((F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x))
  · intro t ht
    rw [interior_Icc] at ht ⊢
    have hd := (hC.scalar_evolution n M J F t (hJ ⟨ht.1.le, ht.2.le⟩) x).mono
      (Ioo_subset_Icc_self.trans hJ)
    simpa only [one_mul, id_eq, Pi.mul_def, Pi.sub_def] using
      ((hasDerivWithinAt_id t (Ioo a b)).sub_const a).mul hd
  · intro t ht
    rw [interior_Icc] at ht
    have htpos : 0 < t - a := sub_pos.mpr ht.1
    have h := mul_nonneg htpos.le (harnack t ht)
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt htpos)] at h
    linarith



theorem curvatureTensorNorm_le_of_terminal_scalar_bound
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a b δ S : ℝ} (hJ : Icc a b ⊆ J) (hδ : 0 < δ) (x : M)
    (hoperator : ∀ t ∈ Icc a b, (F.connection t).NonnegativeCurvatureOperator x)
    (harnack : ∀ t ∈ Ioo a b,
      0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x +
        (F.connection t).scalarCurvature x / (t - a))
    (hterminal : (F.connection b).scalarCurvature x ≤ S)
    {t : ℝ} (ht : t ∈ Icc (a + δ) b) :
    (F.connection t).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * ((b - a) * S / δ) := by
  have hat : a ≤ t := by linarith [ht.1]
  have hab : a ≤ b := hat.trans ht.2
  have hD := hC.tensor_calculus n M (F.metric t) (F.connection t)
  have hnonneg := ((F.connection t).curvatureOperatorBound_scalarCurvature
    hD x (hoperator t ⟨hat, ht.2⟩)).1
  have hmono := monotoneOn_time_mul_scalarCurvature_of_harnack hC F hJ x harnack
    ⟨hat, ht.2⟩ ⟨hab, le_rfl⟩ ht.2
  have htop := mul_le_mul_of_nonneg_left hterminal (sub_nonneg.mpr hab)
  have hweight := mul_le_mul_of_nonneg_right
    (show δ ≤ t - a by linarith [ht.1]) hnonneg
  have hscalar : (F.connection t).scalarCurvature x ≤ (b - a) * S / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith [hmono, htop, hweight]
  exact ((F.connection t).curvatureTensorNorm_le_scalarCurvature hD x
    (hoperator t ⟨hat, ht.2⟩)).trans
      (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _))



theorem curvatureTensorNorm_bound_of_initial_and_terminal
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a b δ K S : ℝ} (hJ : Icc a b ⊆ J) (hδ : 0 < δ)
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (harnack : ∀ x : M, ∀ t ∈ Ioo a b,
      0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x +
        (F.connection t).scalarCurvature x / (t - a))
    (hinitial : ∀ t ∈ Icc a (a + δ), ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ K)
    (hterminal : ∀ x : M, (F.connection b).scalarCurvature x ≤ S) :
    ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤
      max K ((n : ℝ) ^ 2 * ((b - a) * S / δ)) := by
  intro t ht x
  rcases le_total t (a + δ) with hleft | hright
  · exact (hinitial t ⟨ht.1, hleft⟩ x).trans (le_max_left _ _)
  · exact (curvatureTensorNorm_le_of_terminal_scalar_bound hC F hJ hδ x
      (fun s hs => hoperator s hs x) (harnack x) (hterminal x)
      ⟨hright, ht.2⟩).trans (le_max_right _ _)




theorem exists_uniform_curvatureTensorNorm_bound_on_set_of_local_right_bound_and_harnack
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (C : Set M)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (hoperator : ∀ t ∈ Icc a b, ∀ x ∈ C,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hslice : ∀ t ∈ Icc a b, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ C, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x)
    (hright : ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
      ∀ t ∈ Icc c d, ∀ x ∈ C, (F.connection t).curvatureTensorNorm x ≤ K)
    (harnack : ∀ c ∈ Ioc a b,
      (∃ K : ℝ, ∀ t ∈ Icc a c, ∀ x ∈ C,
        (F.connection t).curvatureTensorNorm x ≤ K) →
      ∀ x ∈ C, ∀ t ∈ Ioo a c,
        0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x +
          (F.connection t).scalarCurvature x / (t - a)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x ∈ C,
      (F.connection t).curvatureTensorNorm x ≤ K := by
  have hnorm_scalar (t : ℝ) (ht : t ∈ Icc a b) (x : M) (hx : x ∈ C) :=
    (F.connection t).curvatureTensorNorm_le_scalarCurvature
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) x (hoperator t ht x hx)
  have hslice' : ∀ t ∈ Icc a b, ∃ K : ℝ, ∀ x : C,
      (F.connection t).scalarCurvature x.val ≤ K := by
    intro t ht
    obtain ⟨K, hK, hbound⟩ := hslice t ht
    refine ⟨(n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * K), ?_⟩
    intro x
    have hnorm := (F.connection t).curvatureTensorNorm_le_of_operator_bound
      x.val K hK (hbound x.val x.property)
      (hC.tensor_calculus n M (F.metric t) (F.connection t))
    exact (le_abs_self _).trans
      (((F.connection t).abs_scalarCurvature_le_curvatureTensorNorm x.val).trans
        (mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)))
  have hright' : ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
      ∀ t ∈ Icc c d, ∀ x : C, (F.connection t).scalarCurvature x.val ≤ K := by
    intro c hc
    obtain ⟨d, hd, K, hK⟩ := hright c hc
    refine ⟨d, hd, (n : ℝ) ^ 2 * K, ?_⟩
    intro t ht x
    exact (le_abs_self _).trans
      (((F.connection t).abs_scalarCurvature_le_curvatureTensorNorm x.val).trans
        (mul_le_mul_of_nonneg_left (hK t ht x.val x.property) (sq_nonneg _)))
  have harnack' : ∀ c ∈ Ioc a b,
      (∃ K : ℝ, ∀ t ∈ Icc a c, ∀ x : C, (F.connection t).scalarCurvature x.val ≤ K) →
      ∀ x : C, MonotoneOn (fun t => (t - a) * (F.connection t).scalarCurvature x.val)
        (Icc a c) := by
    intro c hc hbounded x
    have hJc : Icc a c ⊆ J := (Icc_subset_Icc_right hc.2).trans hJ
    apply monotoneOn_time_mul_scalarCurvature_of_harnack hC F hJc x.val
    apply harnack c hc _ x.val x.property
    obtain ⟨K, hK⟩ := hbounded
    refine ⟨(n : ℝ) ^ 2 * K, ?_⟩
    intro t ht x hx
    exact (hnorm_scalar t ⟨ht.1, ht.2.trans hc.2⟩ x hx).trans
      (mul_le_mul_of_nonneg_left (hK t ht ⟨x, hx⟩) (sq_nonneg _))
  obtain ⟨S, hS⟩ := Poincare.RicciFlow.Harnack.exists_uniform_bound_of_local_right_bound_and_harnack
    (fun (x : C) t => (F.connection t).scalarCurvature x.val) hab
    (fun x => (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
      hC J F x.val).mono hJ)
    (fun t ht x => ((F.connection t).curvatureOperatorBound_scalarCurvature
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) x.val
        (hoperator t ht x.val x.property)).1)
    hslice' hright' harnack'
  refine ⟨max 0 ((n : ℝ) ^ 2 * S), le_max_left _ _, ?_⟩
  intro t ht x hx
  exact (hnorm_scalar t ht x hx).trans
    ((mul_le_mul_of_nonneg_left (hS t ht ⟨x, hx⟩) (sq_nonneg _)).trans (le_max_right _ _))



theorem exists_uniform_curvatureTensorNorm_bound_component_of_local_right_bound
    [T3Space M] [SecondCountableTopology M]
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) (O : M)
    (S : RicciFlow.SmoothExhaustion F O)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : MetricComplete (F.metric a))
    (hcurv : ∀ t ∈ Icc a b, ∀ x, (F.metric a).edist O x ≠ ⊤ →
      (F.connection t).NonnegativeCurvatureOperator x)
    (hslice : ∀ t ∈ Icc a b, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x, (F.metric a).edist O x ≠ ⊤ →
        LeviCivitaData.CurvatureOperatorBound (F.connection t) K x)
    (hright : ∀ c ∈ Ico a b, ∃ d ∈ Ioc c b, ∃ K : ℝ,
      ∀ t ∈ Icc c d, ∀ x, (F.metric a).edist O x ≠ ⊤ →
        (F.connection t).curvatureTensorNorm x ≤ K) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      (F.metric a).edist O x ≠ ⊤ → (F.connection t).curvatureTensorNorm x ≤ K := by
  apply exists_uniform_curvatureTensorNorm_bound_on_set_of_local_right_bound_and_harnack
    hC F {x | (F.metric a).edist O x ≠ ⊤} hab hJ hcurv hslice hright
  intro c hc hbounded x hx t ht
  obtain ⟨K, hK⟩ := hbounded
  exact scalar_harnack_on_bounded_slab_component_of_smoothExhaustion hC F O S
    hc.1 ((Icc_subset_Icc_right hc.2).trans hJ) hcomplete hK
    (fun s hs => hcurv s ⟨hs.1, hs.2.trans hc.2⟩) t ⟨ht.1, ht.2.le⟩ x hx

end Poincare.RicciFlow.Harnack
