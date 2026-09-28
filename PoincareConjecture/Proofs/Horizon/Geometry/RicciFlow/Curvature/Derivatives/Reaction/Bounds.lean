import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Derivatives.Reaction.Terms
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def curvatureReactionWeight : ℕ → ℕ
  | 0 => 12
  | m + 1 => 2 * curvatureReactionWeight m + 6 * m + 25

private theorem reactionListEvaluation_append (D : LeviCivitaData g)
    {m : ℕ} (L₁ L₂ : List (ReactionTerm m)) :
    reactionListEvaluation D (L₁ ++ L₂) =
      fun x v ↦ reactionListEvaluation D L₁ x v + reactionListEvaluation D L₂ x v := by
  funext x v
  simp [reactionListEvaluation, List.map_append, List.sum_append]

private theorem isSmoothCovariantTensor_reactionTermEvaluation
    (D : LeviCivitaData g) {m : ℕ} (T : ReactionTerm m) :
    IsSmoothCovariantTensor (reactionTermEvaluation D T) := by
  classical
  by_cases hneg : T.negative = true
  · have hC := isSmoothCovariantTensor_curvaturePairContraction D
      T.leftOrder T.rightOrder T.slots
    constructor
    · intro x
      obtain ⟨A, hA⟩ := hC.1 x
      refine ⟨-A, ?_⟩
      intro v
      simp only [reactionTermEvaluation, hneg, ↓reduceIte, neg_apply, hA]
    · intro U hU X hX
      have h := hC.2 U hU X hX
      simpa only [reactionTermEvaluation, hneg, ↓reduceIte, Pi.neg_apply] using h.neg
  · have hC := isSmoothCovariantTensor_curvaturePairContraction D
      T.leftOrder T.rightOrder T.slots
    constructor
    · intro x
      obtain ⟨A, hA⟩ := hC.1 x
      refine ⟨A, ?_⟩
      intro v
      simp [reactionTermEvaluation, hneg, hA]
    · intro U hU X hX
      have h := hC.2 U hU X hX
      convert h using 1 <;> ext y <;> simp [reactionTermEvaluation, hneg]

private theorem isSmoothCovariantTensor_reactionListEvaluation
    (D : LeviCivitaData g) {m : ℕ} (L : List (ReactionTerm m)) :
    IsSmoothCovariantTensor (reactionListEvaluation D L) := by
  classical
  induction L with
  | nil =>
      constructor
      · intro x
        refine ⟨0, ?_⟩
        intro v
        simp [reactionListEvaluation]
      · intro U hU X hX
        simp only [reactionListEvaluation, List.map_nil, List.sum_nil]
        exact contMDiffOn_const
  | cons T L ih =>
      have hT := isSmoothCovariantTensor_reactionTermEvaluation D T
      constructor
      · intro x
        obtain ⟨A, hA⟩ := hT.1 x
        obtain ⟨B, hB⟩ := ih.1 x
        refine ⟨A + B, ?_⟩
        intro v
        change reactionTermEvaluation D T x v + reactionListEvaluation D L x v = A v + B v
        rw [hA, hB]
      · intro U hU X hX
        have hT' := hT.2 U hU X hX
        have hL' := ih.2 U hU X hX
        change ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
          (fun x ↦ reactionTermEvaluation D T x (fun i ↦ X i x) +
            reactionListEvaluation D L x (fun i ↦ X i x)) U
        convert hT'.add hL' using 1 <;> ext y <;> rfl

private theorem mdifferentiableAt_reactionListEvaluation_extend
    (D : LeviCivitaData g) {m : ℕ} (L : List (ReactionTerm m)) (x : M)
    (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun (y : M) ↦ reactionListEvaluation D L y
        (fun i : Fin (4 + m) ↦ FiberBundle.extend
          (EuclideanSpace ℝ (Fin n)) (v i) y)) x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let S := fun i : Fin (4 + m) ↦
    FiberBundle.extend E (v i)
  choose U hU hS using fun i : Fin (4 + m) =>
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) E (v i)
  have hInt : (⋂ i : Fin (4 + m), U i) ∈ 𝓝 x :=
    Filter.iInter_mem.2 hU
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hInt
  have hlist := isSmoothCovariantTensor_reactionListEvaluation D L
  have hfields : ∀ i : Fin (4 + m),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, E))) ∞ (T% (S i)) V := by
    intro i
    exact (hS i).mono (fun y hy => (Set.mem_iInter.mp (hVsub hy)) i)
  have hscalar := hlist.2 V hVopen S hfields
  have hat := hscalar.contMDiffAt (hVopen.mem_nhds hxV)
  exact hat.mdifferentiableAt (by simp)

private theorem covariantTensorDerivative_reactionListEvaluation_cons
    (D : LeviCivitaData g) {m : ℕ} (T : ReactionTerm m)
    (L : List (ReactionTerm m)) :
    D.covariantTensorDerivative (reactionListEvaluation D (T :: L)) =
      fun x v ↦ D.covariantTensorDerivative (reactionTermEvaluation D T) x v +
        D.covariantTensorDerivative (reactionListEvaluation D L) x v := by
  classical
  funext x v
  have hT := mdifferentiableAt_reactionListEvaluation_extend D [T] x
    (fun i : Fin (4 + m) ↦ v i.succ)
  have hL := mdifferentiableAt_reactionListEvaluation_extend D L x
    (fun i : Fin (4 + m) ↦ v i.succ)
  have hT' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun (y : M) ↦ reactionTermEvaluation D T y
        (fun i : Fin (4 + m) ↦ FiberBundle.extend
          (EuclideanSpace ℝ (Fin n)) (v i.succ) y)) x := by
    simpa [reactionListEvaluation] using hT
  change D.covariantTensorDerivative
      (fun y w ↦ reactionTermEvaluation D T y w + reactionListEvaluation D L y w) x v = _
  simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero,
    Fin.cons_succ, mvfderiv_fun_add hT' hL, sub_apply,
    Finset.sum_add_distrib, add_apply]
  ring

private theorem reactionTerm_derivative_expansion (D : LeviCivitaData g)
    {m : ℕ} (T : ReactionTerm m) :
    ∃ T₁ T₂ : ReactionTerm (m + 1),
      D.covariantTensorDerivative (reactionTermEvaluation D T) =
        fun x v ↦ reactionTermEvaluation D T₁ x v +
          reactionTermEvaluation D T₂ x v := by
  classical
  obtain ⟨σL, σR, hσ⟩ := exists_curvaturePairContraction_derivative_slots D
    T.leftOrder T.rightOrder T.slots
  let T₁ : ReactionTerm (m + 1) :=
    { leftOrder := T.leftOrder + 1
      rightOrder := T.rightOrder
      orders_eq := by
        have horders := T.orders_eq
        omega
      negative := T.negative
      slots := σL }
  let T₂ : ReactionTerm (m + 1) :=
    { leftOrder := T.leftOrder
      rightOrder := T.rightOrder + 1
      orders_eq := by
        have horders := T.orders_eq
        omega
      negative := T.negative
      slots := σR }
  have hnegder (S : CovariantTensorEvaluation n M (4 + m)) :
      D.covariantTensorDerivative (fun y w ↦ -S y w) =
        fun x v ↦ -D.covariantTensorDerivative S x v := by
    funext x v
    simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero,
      Fin.cons_succ, mvfderiv_fun_neg, neg_apply, Function.update,
      Finset.sum_neg_distrib]
    ring
  by_cases hneg : T.negative = true
  · refine ⟨T₁, T₂, ?_⟩
    have h := hnegder (curvaturePairContraction D T.leftOrder T.rightOrder T.slots)
    rw [show reactionTermEvaluation D T =
        (fun x v ↦ -curvaturePairContraction D T.leftOrder T.rightOrder T.slots x v) by
          funext x v; simp [reactionTermEvaluation, hneg]]
    rw [h]
    simp only [T₁, T₂, reactionTermEvaluation, hneg, ↓reduceIte]
    rw [hσ]
    funext x v
    ring
  · refine ⟨T₁, T₂, ?_⟩
    have hfalse : T.negative = false := by
      cases h : T.negative <;> simp_all
    have heval : reactionTermEvaluation D T =
        curvaturePairContraction D T.leftOrder T.rightOrder T.slots := by
      funext y v
      simp [reactionTermEvaluation, hneg]
    calc
      D.covariantTensorDerivative (reactionTermEvaluation D T) =
          D.covariantTensorDerivative
            (curvaturePairContraction D T.leftOrder T.rightOrder T.slots) := by
        rw [heval]
      _ = fun y v ↦
          curvaturePairContraction D (T.leftOrder + 1) T.rightOrder σL y v +
            curvaturePairContraction D T.leftOrder (T.rightOrder + 1) σR y v := hσ
      _ = fun y v ↦ reactionTermEvaluation D T₁ y v +
          reactionTermEvaluation D T₂ y v := by
        funext y v
        simp [T₁, T₂, reactionTermEvaluation, hfalse]

private theorem reactionList_derivative_expansion (D : LeviCivitaData g)
    {m : ℕ} (L : List (ReactionTerm m)) :
    ∃ L' : List (ReactionTerm (m + 1)),
      L'.length = 2 * L.length ∧
      D.covariantTensorDerivative (reactionListEvaluation D L) =
        reactionListEvaluation D L' := by
  classical
  induction L with
  | nil =>
      refine ⟨[], by simp, ?_⟩
      funext x v
      simp [reactionListEvaluation, LeviCivitaData.covariantTensorDerivative,
        mvfderiv_const, Finset.sum_const_zero]
  | cons T L ih =>
      obtain ⟨T₁, T₂, hT⟩ := reactionTerm_derivative_expansion D T
      obtain ⟨L', hLlen, hL⟩ := ih
      refine ⟨T₁ :: T₂ :: L', ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · rw [covariantTensorDerivative_reactionListEvaluation_cons D T L, hT, hL]
        funext x v
        simp [reactionListEvaluation]
        ring

private theorem curvatureDerivativeReaction_representation
    (D : LeviCivitaData g) (m : ℕ) :
    ∃ L : List (ReactionTerm m), L.length = curvatureReactionWeight m ∧
      curvatureDerivativeReaction D m = reactionListEvaluation D L := by
  induction m with
  | zero =>
      obtain ⟨L, hlen, heval⟩ := curvatureReaction_base_expansion D
      exact ⟨L, by simpa [curvatureReactionWeight] using hlen,
        by simpa [curvatureDerivativeReaction] using heval⟩
  | succ m ih =>
      obtain ⟨L, hLlen, hL⟩ := ih
      obtain ⟨Ld, hLdlen, hLd⟩ := reactionList_derivative_expansion D L
      obtain ⟨Lc, hLclen, hLc⟩ := tensorHeatCorrection_expansion D m
      refine ⟨Ld ++ Lc, ?_, ?_⟩
      · simp only [List.length_append]
        simp only [curvatureReactionWeight] at *
        omega
      · have hder := congrArg D.covariantTensorDerivative hL
        rw [curvatureDerivativeReaction, hder, hLd, hLc,
          reactionListEvaluation_append]

private theorem tensorNorm_reactionTermEvaluation_le (D : LeviCivitaData g)
    {m : ℕ} (T : ReactionTerm m) (x : M) :
    g.tensorNorm (reactionTermEvaluation D T) x ≤
      (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        D.curvatureDerivativeNorm T.leftOrder x * D.curvatureDerivativeNorm T.rightOrder x := by
  have h := tensorNorm_curvaturePairContraction_le D T.leftOrder T.rightOrder
    (k := 4 + m) T.slots x
  by_cases hneg : T.negative = true
  · simpa [reactionTermEvaluation, hneg, RiemannianMetric.tensorNorm,
      sq, mul_assoc] using h
  · have heval : reactionTermEvaluation D T =
        curvaturePairContraction D T.leftOrder T.rightOrder T.slots := by
      funext y v
      simp [reactionTermEvaluation, hneg]
    rw [heval]
    exact h

private noncomputable def reactionListComponents (D : LeviCivitaData g)
    {m : ℕ} (L : List (ReactionTerm m)) (x : M) :
    EuclideanSpace ℝ
      (Fin (4 + m) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
  WithLp.toLp 2
    (fun a : Fin (4 + m) → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ↦
      reactionListEvaluation D L x
        (fun i : Fin (4 + m) ↦ g.orthonormalBasis x (a i)))

private theorem reactionListComponents_cons (D : LeviCivitaData g)
    {m : ℕ} (T : ReactionTerm m) (L : List (ReactionTerm m)) (x : M) :
    reactionListComponents D (T :: L) x =
      reactionListComponents D [T] x + reactionListComponents D L x := by
  apply congrArg (WithLp.toLp 2)
  funext a
  simp [reactionListComponents, reactionListEvaluation, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

private theorem norm_reactionListComponents (D : LeviCivitaData g)
    {m : ℕ} (L : List (ReactionTerm m)) (x : M) :
    ‖reactionListComponents D L x‖ = g.tensorNorm (reactionListEvaluation D L) x := by
  classical
  rw [EuclideanSpace.norm_eq]
  simp only [reactionListComponents, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs]
  rfl

private theorem tensorNorm_reactionListEvaluation_le_sum (D : LeviCivitaData g)
    {m : ℕ} (L : List (ReactionTerm m)) (x : M) :
    g.tensorNorm (reactionListEvaluation D L) x ≤
      (L.map (fun T ↦ g.tensorNorm (reactionTermEvaluation D T) x)).sum := by
  classical
  induction L with
  | nil => simp [reactionListEvaluation, RiemannianMetric.tensorNorm]
  | cons T L ih =>
      have hvec := reactionListComponents_cons D T L x
      have hnorm := norm_add_le (reactionListComponents D [T] x)
        (reactionListComponents D L x)
      rw [← hvec, norm_reactionListComponents D (T :: L) x,
        norm_reactionListComponents D [T] x,
        norm_reactionListComponents D L x] at hnorm
      have hsingleton : g.tensorNorm (reactionListEvaluation D [T]) x =
          g.tensorNorm (reactionTermEvaluation D T) x := by
        have heval : reactionListEvaluation D [T] = reactionTermEvaluation D T := by
          funext y v
          simp [reactionListEvaluation]
        rw [heval]
      calc
        g.tensorNorm (reactionListEvaluation D (T :: L)) x ≤
            g.tensorNorm (reactionListEvaluation D [T]) x +
              g.tensorNorm (reactionListEvaluation D L) x := hnorm
        _ = g.tensorNorm (reactionTermEvaluation D T) x +
              g.tensorNorm (reactionListEvaluation D L) x := by rw [hsingleton]
        _ ≤ g.tensorNorm (reactionTermEvaluation D T) x +
              (L.map (fun T ↦ g.tensorNorm (reactionTermEvaluation D T) x)).sum :=
          by
            simpa [add_comm] using
              add_le_add_right ih (g.tensorNorm (reactionTermEvaluation D T) x)
        _ = (List.map (fun T ↦ g.tensorNorm (reactionTermEvaluation D T) x) (T :: L)).sum := by
          simp [List.map_cons]

private theorem tensorNorm_reactionTermEvaluation_le_orderSum
    (D : LeviCivitaData g) {m : ℕ} (T : ReactionTerm m) (x : M) :
    g.tensorNorm (reactionTermEvaluation D T) x ≤
      (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (∑ i ∈ Finset.range (m + 1),
          D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x) := by
  have hterm := tensorNorm_reactionTermEvaluation_le D T x
  have hnon : ∀ i ∈ Finset.range (m + 1),
      0 ≤ D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x := by
    intro i hi
    exact mul_nonneg
      (by unfold LeviCivitaData.curvatureDerivativeNorm RiemannianMetric.tensorNorm
          exact Real.sqrt_nonneg _)
      (by unfold LeviCivitaData.curvatureDerivativeNorm RiemannianMetric.tensorNorm
          exact Real.sqrt_nonneg _)
  have hmem : T.leftOrder ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    have horders : T.leftOrder + T.rightOrder = m := T.orders_eq
    omega
  have hprod : D.curvatureDerivativeNorm T.leftOrder x *
      D.curvatureDerivativeNorm T.rightOrder x ≤
      ∑ i ∈ Finset.range (m + 1),
        D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x := by
    have hs := Finset.single_le_sum hnon hmem
    have horders : T.leftOrder + T.rightOrder = m := T.orders_eq
    simpa [show m - T.leftOrder = T.rightOrder by omega] using hs
  have hterm' : g.tensorNorm (reactionTermEvaluation D T) x ≤
      (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (D.curvatureDerivativeNorm T.leftOrder x *
          D.curvatureDerivativeNorm T.rightOrder x) := by
    simpa only [mul_assoc] using hterm
  exact hterm'.trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _))

private theorem tensorNorm_reactionListEvaluation_le (D : LeviCivitaData g)
    {m : ℕ} (L : List (ReactionTerm m)) (x : M) :
    g.tensorNorm (reactionListEvaluation D L) x ≤
      (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) * (L.length : ℝ) *
        (∑ i ∈ Finset.range (m + 1),
          D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x) := by
  classical
  induction L with
  | nil =>
      have hzero : reactionListEvaluation D ([] : List (ReactionTerm m)) = 0 := by
        funext y v
        simp [reactionListEvaluation]
      rw [hzero]
      simp [RiemannianMetric.tensorNorm]
  | cons T L ih =>
      have hT := tensorNorm_reactionTermEvaluation_le_orderSum D T x
      have hvec := reactionListComponents_cons D T L x
      have hnorm := norm_add_le (reactionListComponents D [T] x)
        (reactionListComponents D L x)
      rw [← hvec, norm_reactionListComponents D (T :: L) x,
        norm_reactionListComponents D [T] x,
        norm_reactionListComponents D L x] at hnorm
      have hsingleton : g.tensorNorm (reactionListEvaluation D [T]) x =
          g.tensorNorm (reactionTermEvaluation D T) x := by
        have heval : reactionListEvaluation D [T] = reactionTermEvaluation D T := by
          funext y v
          simp [reactionListEvaluation]
        rw [heval]
      calc
        g.tensorNorm (reactionListEvaluation D (T :: L)) x ≤
            g.tensorNorm (reactionTermEvaluation D T) x +
              g.tensorNorm (reactionListEvaluation D L) x := by
          simpa [hsingleton] using hnorm
        _ ≤ (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
              (∑ i ∈ Finset.range (m + 1),
                D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x) +
            (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) * (L.length : ℝ) *
              (∑ i ∈ Finset.range (m + 1),
                D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x) :=
          add_le_add hT ih
        _ = (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
              ((T :: L).length : ℝ) *
              (∑ i ∈ Finset.range (m + 1),
                D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

theorem tensorNorm_curvatureDerivativeReaction_le (D : LeviCivitaData g)
    (m : ℕ) (x : M) :
    g.tensorNorm (curvatureDerivativeReaction D m) x ≤
      (Module.finrank ℝ (TangentSpace (𝓡 n) x) : ℝ) *
        (curvatureReactionWeight m : ℝ) *
        (∑ i ∈ Finset.range (m + 1),
          D.curvatureDerivativeNorm i x * D.curvatureDerivativeNorm (m - i) x) := by
  obtain ⟨L, hlen, hrep⟩ := curvatureDerivativeReaction_representation D m
  rw [hrep]
  have h := tensorNorm_reactionListEvaluation_le D L x
  simpa [hlen, mul_assoc] using h

end PoincareConjecture.RicciFlowAnalysis
