import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def tensorTraceLast (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M (k + 2)) : CovariantTensorEvaluation n M k :=
  fun x v ↦ ∑ i, T x (Fin.append v ![g.orthonormalBasis x i, g.orthonormalBasis x i])

private theorem append_update_left {α : Type*} {k l : ℕ}
    (v : Fin k → α) (w : Fin l → α) (i : Fin k) (a : α) :
    Function.update (Fin.append v w) (Fin.castAdd l i) a =
      Fin.append (Function.update v i a) w := by
  classical
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro b
    by_cases hb : b = i
    · subst b
      simp only [Function.update_self, Fin.append_left]
    · have hne : Fin.castAdd l b ≠ Fin.castAdd l i := by
        intro he
        apply hb
        exact Fin.castAdd_injective k l he
      simp only [Function.update_of_ne hne, Fin.append_left, Function.update_of_ne hb]
  · intro b
    have hne : Fin.natAdd k b ≠ Fin.castAdd l i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp only [Function.update_of_ne hne, Fin.append_right]

private theorem append_update_right {α : Type*} {k l : ℕ}
    (v : Fin k → α) (w : Fin l → α) (i : Fin l) (a : α) :
    Function.update (Fin.append v w) (Fin.natAdd k i) a =
      Fin.append v (Function.update w i a) := by
  classical
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro b
    have hne : Fin.castAdd l b ≠ Fin.natAdd k i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    simp only [Function.update_of_ne hne, Fin.append_left]
  · intro b
    by_cases hb : b = i
    · subst b
      simp only [Function.update_self, Fin.append_right]
    · have hne : Fin.natAdd k b ≠ Fin.natAdd k i := by
        intro he
        apply hb
        apply Fin.ext
        have hv := congrArg Fin.val he
        simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hv
      simp only [Function.update_of_ne hne, Fin.append_right, Function.update_of_ne hb]

omit [IsManifold (𝓡 n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
private theorem mvfderiv_clm_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : M → E →L[ℝ] F} {v : M → E} {x : M}
    (hL : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] F) L x)
    (hv : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) v x) (a : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y ↦ L y (v y)) x a =
      L x (mvfderiv (𝓡 n) v x a) + mvfderiv (𝓡 n) L x a (v x) := by
  have happ := (hasFDerivAt_fst (𝕜 := ℝ) (p := (L x, v x))).clm_apply
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (L x, v x)))
  have hm := happ.hasMFDerivAt.comp x (hL.hasMFDerivAt.prodMk hv.hasMFDerivAt)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply] using!
    congrArg (fun K ↦ K a) hm.mfderiv

omit [IsManifold (𝓡 n) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
private theorem mvfderiv_clm_const {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : M → E →L[ℝ] F} {x : M}
    (hL : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] F) L x)
    (a : TangentSpace (𝓡 n) x) (v : E) :
    mvfderiv (𝓡 n) (fun y ↦ L y v) x a = mvfderiv (𝓡 n) L x a v := by
  simpa only [mvfderiv_const, zero_apply, map_zero, zero_add] using!
    mvfderiv_clm_apply hL (mdifferentiableAt_const (c := v)) a

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_product_rule {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U) {A : (x : M) → TangentSpace (𝓡 n) x}
    {V : Fin k → (x : M) → TangentSpace (𝓡 n) x}
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦ V i y)) x (A x) =
      D.covariantTensorDerivative T x (Fin.cons (A x) (fun i ↦ V i x)) +
        ∑ i, T x (Function.update (fun j ↦ V j x) i (D.connection (V i) x (A x))) := by
  let AV : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y := Fin.cons A V
  have hAV (i : Fin (k + 1)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (AV i)) U := by
    cases i using Fin.cases with
    | zero => exact hA
    | succ i => exact hV i
  have he := covariantTensorDerivativeOnFields_eq D hT hU hAV hx
  have hpoint : (fun i ↦ AV i x) = Fin.cons (A x) (fun i ↦ V i x) := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [hpoint] at he
  simp only [covariantTensorDerivativeOnFields, AV, Fin.cons_succ, Fin.cons_zero] at he
  exact sub_eq_iff_eq_add.mp he

set_option maxHeartbeats 1500000 in

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_trace_representation (g : RiemannianMetric n M) {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {V : Fin k → (x : M) → TangentSpace (𝓡 n) x}
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) (x : M) (hx : x ∈ U) :
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
    ∃ L : M → E →L[ℝ] E,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ L x ∧
      (∀ y ∈ U ∩ e.baseSet, ∀ a b : E,
        g.inner y (e.symmL ℝ y (L y a)) (e.symmL ℝ y b) =
          T y (Fin.append (fun i ↦ V i y) ![e.symmL ℝ y a, e.symmL ℝ y b])) ∧
      ∀ y ∈ U ∩ e.baseSet,
        LinearMap.trace ℝ E (L y).toLinearMap = tensorTraceLast g T y (fun i ↦ V i y) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  choose P hP using hT.1
  let R := fun y a b ↦ T y (Fin.append (fun i ↦ V i y) ![a, b])
  have hRT (y : M) (a b : TangentSpace (𝓡 n) y) :
      R y a b = P y (Fin.append (fun i ↦ V i y) ![a, b]) := hP y _
  have hu0 {y : M} (a b z : TangentSpace (𝓡 n) y) :
      Function.update ![a, b] 0 z = ![z, b] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu1 {y : M} (a b z : TangentSpace (𝓡 n) y) :
      Function.update ![a, b] 1 z = ![a, z] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have ha1 (y : M) (a b c : TangentSpace (𝓡 n) y) :
      R y (a + b) c = R y a c + R y b c := by
    simp only [hRT]
    simpa only [append_update_right, hu0] using
      (P y).map_update_add (Fin.append (fun i ↦ V i y) ![a, c]) (Fin.natAdd k 0) a b
  have ha2 (y : M) (a b c : TangentSpace (𝓡 n) y) :
      R y c (a + b) = R y c a + R y c b := by
    simp only [hRT]
    simpa only [append_update_right, hu1] using
      (P y).map_update_add (Fin.append (fun i ↦ V i y) ![c, a]) (Fin.natAdd k 1) a b
  have hs1 (y : M) (c : ℝ) (a b : TangentSpace (𝓡 n) y) :
      R y (c • a) b = c • R y a b := by
    simp only [hRT]
    simpa only [append_update_right, hu0] using
      (P y).map_update_smul (Fin.append (fun i ↦ V i y) ![a, b]) (Fin.natAdd k 0) c a
  have hs2 (y : M) (c : ℝ) (a b : TangentSpace (𝓡 n) y) :
      R y a (c • b) = c • R y a b := by
    simp only [hRT]
    simpa only [append_update_right, hu1] using
      (P y).map_update_smul (Fin.append (fun i ↦ V i y) ![a, b]) (Fin.natAdd k 1) c b
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let O := U ∩ e.baseSet
  have hO : IsOpen O := hU.inter e.open_baseSet
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hxO : x ∈ O := ⟨hx, hxe⟩
  let S := fun y ↦ e.symmL ℝ y
  have hSext (v : E) {y : M} (hy : y ∈ e.baseSet) :
      FiberBundle.extend E (S x v) y = S y v := by
    change e.symm y (e ⟨x, e.symmL ℝ x v⟩).2 = e.symmL ℝ y v
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hxe,
      e.continuousLinearMapAt_symmL hxe, e.symmL_apply hy]
  have hS (v : E) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
      ∞ (T% (fun y ↦ S y v)) e.baseSet := by
    apply (contMDiffOn_extend_baseSet (S x v)).congr
    intro y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext v hy).symm
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    (g.inner y).bilinearComp (S y) (S y)
  let C : M → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    LinearMap.toContinuousLinearMap
      { toFun := fun v ↦ LinearMap.toContinuousLinearMap
          { toFun := fun w ↦ R y (S y v) (S y w)
            map_add' := by intro a b; rw [map_add, ha2]
            map_smul' := by intro c a; rw [map_smul, hs2]; rfl }
        map_add' := by
          intro a b
          ext w
          change R y (S y (a + b)) (S y w) = _
          rw [map_add, ha1]
          rfl
        map_smul' := by
          intro c a
          ext w
          change R y (S y (c • a)) (S y w) = _
          rw [map_smul, hs1]
          rfl }
  have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B x := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply contMDiffAt_clm_of_apply
    intro w
    exact ((hS v).inner_bundle (hS w)).contMDiffAt (e.open_baseSet.mem_nhds hxe)
  have hC : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ C x := by
    apply contMDiffAt_clm_of_apply
    intro v
    apply contMDiffAt_clm_of_apply
    intro w
    let W : Fin (k + 2) → (y : M) → TangentSpace (𝓡 n) y :=
      Fin.append V ![fun y ↦ S y v, fun y ↦ S y w]
    have hW (i : Fin (k + 2)) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
        ∞ (T% (W i)) O := by
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [W, Fin.append_left] using (hV j).mono Set.inter_subset_left
      · intro j
        fin_cases j
        · simpa [W, Fin.append_right] using!
            (hS v).mono Set.inter_subset_right
        · simpa [W, Fin.append_right] using!
            (hS w).mono Set.inter_subset_right
    have hpoint (y : M) : (fun i ↦ W i y) = Fin.append (fun i ↦ V i y) ![S y v, S y w] := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [W, Fin.append_left]
      · intro j
        simp only [W, Fin.append_right]
        fin_cases j <;> rfl
    simpa only [hpoint] using! (hT.2 O hO W hW).contMDiffAt (hO.mem_nhds hxO)
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let G : M → E →L[ℝ] E := fun y ↦ Q.toContinuousLinearMap.comp (B y)
  let H : M → E →L[ℝ] E := fun y ↦ Q.toContinuousLinearMap.comp (C y)
  have hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ G x := contMDiffAt_const.clm_comp hB
  have hH : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ H x := contMDiffAt_const.clm_comp hC
  have hInv {y : M} (hy : y ∈ e.baseSet) : (G y).IsInvertible := by
    have hz (v : E) (hv : G y v = 0) : v = 0 := by
      have hBv : B y v = 0 := Q.injective (by simpa [G] using hv)
      have hi : g.inner y (S y v) (S y v) = 0 := by
        simpa [B] using congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hBv
      have hSv : S y v = 0 := by
        by_contra hne
        exact (ne_of_gt (g.pos y _ hne)) hi
      have hv' := congrArg (e.continuousLinearMapAt ℝ y) hSv
      simpa only [S, e.continuousLinearMapAt_symmL hy, map_zero] using hv'
    have hinj : Function.Injective (G y) := by
      intro v w h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (G y) := LinearMap.injective_iff_surjective.mp hinj
    exact ⟨(LinearEquiv.ofBijective (G y).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext v; rfl⟩
  let L := fun y ↦ (G y).inverse.comp (H y)
  have hL : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E) ∞ L x :=
    ((hInv hxe).contDiffAt_map_inverse.contMDiffAt.comp x hG).clm_comp hH
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let tr := fun y ↦ ∑ i, b.repr (L y (b i)) i
  have htr : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ tr x := by
    apply ContMDiffAt.sum
    intro i _
    exact (b.coord i).toContinuousLinearMap.contMDiffAt.comp x
      (hL.clm_apply contMDiffAt_const)
  have htr_eq (y : M) : LinearMap.trace ℝ E (L y).toLinearMap = tr y := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, tr]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have heq {y : M} (hy : y ∈ e.baseSet) : tr y = tensorTraceLast g T y (fun i ↦ V i y) := by
    let e' := (e.continuousLinearEquivAt ℝ y hy).symm
    let K := e'.toLinearEquiv.conj (L y).toLinearMap
    have hrec (v : E) : B y (L y v) = C y v := by
      apply Q.injective
      change G y ((G y).inverse (H y v)) = H y v
      exact (hInv hy).self_apply_inverse _
    have hK (a b : TangentSpace (𝓡 n) y) : g.inner y (K a) b = R y a b := by
      have h := congrArg (fun f : E →L[ℝ] ℝ ↦ f (e'.symm b)) (hrec (e'.symm a))
      have hSe (v : E) : S y v = e' v :=
        (congrFun (e.symm_continuousLinearEquivAt_eq hy) v).symm
      change g.inner y (S y (L y (e'.symm a))) (S y (e'.symm b)) =
        R y (S y (e'.symm a)) (S y (e'.symm b)) at h
      simp only [hSe, e'.apply_symm_apply] at h
      exact h
    calc
      tr y = LinearMap.trace ℝ E (L y).toLinearMap := (htr_eq y).symm
      _ = LinearMap.trace ℝ (TangentSpace (𝓡 n) y) K :=
        (LinearMap.trace_conj' (L y).toLinearMap e'.toLinearEquiv).symm
      _ = ∑ i, inner ℝ (g.orthonormalBasis y i) (K (g.orthonormalBasis y i)) := by
        rw [LinearMap.trace_eq_matrix_trace ℝ (g.orthonormalBasis y).toBasis]
        simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        change g.inner y (g.orthonormalBasis y i) (K (g.orthonormalBasis y i)) =
          R y (g.orthonormalBasis y i) (g.orthonormalBasis y i)
        rw [g.symm, hK]
  refine ⟨L, hL, ?_, ?_⟩
  · intro y hy a b
    have hh : B y (L y a) = C y a := by
      apply Q.injective
      exact (hInv hy.2).self_apply_inverse (H y a)
    exact congrArg (fun f : E →L[ℝ] ℝ ↦ f b) hh
  · intro y hy
    rw [htr_eq]
    exact heq hy.2

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_tensorTraceLast (g : RiemannianMetric n M) {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {V : Fin k → (x : M) → TangentSpace (𝓡 n) x}
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ tensorTraceLast g T x (fun i ↦ V i x)) U := by
  intro x hx
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  obtain ⟨L, hL, _, htr⟩ := tensor_trace_representation g hT hU hV x hx
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hs : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ LinearMap.trace ℝ E (L y).toLinearMap) x := by
    have heq (y : M) : LinearMap.trace ℝ E (L y).toLinearMap = ∑ i, b.repr (L y (b i)) i := by
      rw [LinearMap.trace_eq_matrix_trace ℝ b]
      simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    simp_rw [heq]
    exact ContMDiffAt.sum (fun i _ ↦ (b.coord i).toContinuousLinearMap.contMDiffAt.comp x
      (hL.clm_apply contMDiffAt_const))
  apply ContMDiffAt.contMDiffWithinAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [(hU.inter e.open_baseSet).mem_nhds
    (show x ∈ U ∩ e.baseSet from ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩)] with y hy
  exact (htr y hy).symm

theorem isSmoothCovariantTensor_tensorTraceLast (g : RiemannianMetric n M) {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (tensorTraceLast g T) := by
  classical
  constructor
  · intro x
    obtain ⟨L, hL⟩ := hT.1 x
    refine ⟨MultilinearMap.mk' (R := ℝ) (tensorTraceLast g T x) ?_ ?_, fun _ ↦ rfl⟩
    · intro v i a b
      simp only [tensorTraceLast, ← append_update_left, hL, L.map_update_add,
        Finset.sum_add_distrib]
    · intro v i c a
      simp only [tensorTraceLast, ← append_update_left, hL, L.map_update_smul,
        Finset.smul_sum]
  · intro U hU V hV
    exact contMDiffOn_tensorTraceLast g hT hU hV

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_trace_product_rule {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U) {A : (x : M) → TangentSpace (𝓡 n) x}
    {V : Fin k → (x : M) → TangentSpace (𝓡 n) x}
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hV : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (V i)) U) {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) (fun y ↦ tensorTraceLast g T y (fun i ↦ V i y)) x (A x) =
      tensorTraceLast g (D.covariantTensorDerivative T) x
        (Fin.cons (A x) (fun i ↦ V i x)) +
      ∑ j, tensorTraceLast g T x
        (Function.update (fun i ↦ V i x) j (D.connection (V j) x (A x))) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let O := U ∩ e.baseSet
  have hO : IsOpen O := hU.inter e.open_baseSet
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hxO : x ∈ O := ⟨hx, hxe⟩
  let S := fun y ↦ e.symmL ℝ y
  have hSext (v : E) {y : M} (hy : y ∈ e.baseSet) :
      FiberBundle.extend E (S x v) y = S y v := by
    change e.symm y (e ⟨x, e.symmL ℝ x v⟩).2 = e.symmL ℝ y v
    rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hxe,
      e.continuousLinearMapAt_symmL hxe, e.symmL_apply hy]
  have hS (v : E) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
      ∞ (T% (fun y ↦ S y v)) e.baseSet := by
    apply (contMDiffOn_extend_baseSet (S x v)).congr
    intro y hy
    exact congrArg (Bundle.TotalSpace.mk y) (hSext v hy).symm
  have hSd (v : E) := ((hS v).contMDiffAt (e.open_baseSet.mem_nhds hxe)).mdifferentiableAt
    (by simp)
  obtain ⟨L, hL, hPair, hTrace⟩ := tensor_trace_representation g hT hU hV x hx
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    (g.inner y).bilinearComp (S y) (S y)
  have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B x := by
    apply contMDiffAt_clm_of_apply
    intro u
    apply contMDiffAt_clm_of_apply
    intro v
    exact ((hS u).inner_bundle (hS v)).contMDiffAt (e.open_baseSet.mem_nhds hxe)
  let C : E →L[ℝ] E := LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ e.continuousLinearMapAt ℝ x
        (D.connection (fun y ↦ S y u) x (A x))
      map_add' := by
        intro u v
        have he : (fun y ↦ S y (u + v)) = (fun y ↦ S y u) + (fun y ↦ S y v) := by
          funext y
          exact map_add (S y) u v
        rw [he, D.connection.isCovariantDerivativeOnUniv.add (hSd u) (hSd v),
          add_apply, map_add]
      map_smul' := by
        intro c u
        have he : (fun y ↦ S y (c • u)) = c • (fun y ↦ S y u) := by
          funext y
          exact map_smul (S y) c u
        rw [he, D.connection.isCovariantDerivativeOnUniv.smul_const c (hSd u),
          smul_apply, map_smul]
        rfl }
  have hC (u : E) : S x (C u) = D.connection (fun y ↦ S y u) x (A x) :=
    e.symmL_continuousLinearMapAt hxe _
  let dL := mvfderiv (𝓡 n) L x (A x)
  let N := dL - (L x).comp C + C.comp (L x)
  have hBd (u v : E) :
      mvfderiv (𝓡 n) B x (A x) u v = B x (C u) v + B x u (C v) := by
    have he : mvfderiv (𝓡 n) (fun y ↦ B y u v) x (A x) =
        mvfderiv (𝓡 n) B x (A x) u v := by
      rw [mvfderiv_clm_const ((hB.clm_apply contMDiffAt_const).mdifferentiableAt (by simp)),
        mvfderiv_clm_const (hB.mdifferentiableAt (by simp))]
    rw [← he]
    change mvfderiv (𝓡 n) (fun y ↦ g.inner y (S y u) (S y v)) x (A x) =
      g.inner x (S x (C u)) (S x v) + g.inner x (S x u) (S x (C v))
    rw [hC, hC]
    exact metric_derivative_pairing D A (hSd u) (hSd v)
  have hu0 (a b z : TangentSpace (𝓡 n) x) :
      Function.update ![a, b] 0 z = ![z, b] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu1 (a b z : TangentSpace (𝓡 n) x) :
      Function.update ![a, b] 1 z = ![a, z] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hN (u v : E) : B x (N u) v =
      D.covariantTensorDerivative T x
        (Fin.cons (A x) (Fin.append (fun i ↦ V i x) ![S x u, S x v])) +
      ∑ j, T x (Fin.append
        (Function.update (fun i ↦ V i x) j (D.connection (V j) x (A x))) ![S x u, S x v]) := by
    let W : Fin (k + 2) → (y : M) → TangentSpace (𝓡 n) y :=
      Fin.append V ![fun y ↦ S y u, fun y ↦ S y v]
    have hW (i : Fin (k + 2)) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
        ∞ (T% (W i)) O := by
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [W, Fin.append_left] using (hV j).mono Set.inter_subset_left
      · intro j
        fin_cases j
        · simpa [W, Fin.append_right] using! (hS u).mono Set.inter_subset_right
        · simpa [W, Fin.append_right] using! (hS v).mono Set.inter_subset_right
    have hpoint (y : M) : (fun i ↦ W i y) =
        Fin.append (fun i ↦ V i y) ![S y u, S y v] := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [W, Fin.append_left]
      · intro j
        simp only [W, Fin.append_right]
        fin_cases j <;> rfl
    have hp := tensor_product_rule D hT hO (hA.mono Set.inter_subset_left) hW hxO
    simp only [hpoint, Fin.sum_univ_add, append_update_left, append_update_right,
      W, Fin.append_left, Fin.append_right, Fin.sum_univ_two, hu0, hu1,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hp
    have hloc : (fun y ↦ B y (L y u) v) =ᶠ[𝓝 x]
        (fun y ↦ T y (Fin.append (fun i ↦ V i y) ![S y u, S y v])) := by
      filter_upwards [hO.mem_nhds hxO] with y hy
      exact hPair y hy u v
    have hd : mvfderiv (𝓡 n) (fun y ↦ B y (L y u) v) x (A x) =
        mvfderiv (𝓡 n)
          (fun y ↦ T y (Fin.append (fun i ↦ V i y) ![S y u, S y v])) x (A x) := by
      have he : mvfderiv (𝓡 n) (fun y ↦ B y (L y u) v) x =
          mvfderiv (𝓡 n)
            (fun y ↦ T y (Fin.append (fun i ↦ V i y) ![S y u, S y v])) x :=
        hloc.mfderiv_eq
      exact congrArg (fun K ↦ K (A x)) he
    rw [mvfderiv_clm_const
      ((hB.clm_apply (hL.clm_apply contMDiffAt_const)).mdifferentiableAt (by simp)),
      mvfderiv_clm_apply (hB.mdifferentiableAt (by simp))
        ((hL.clm_apply contMDiffAt_const).mdifferentiableAt (by simp)),
      add_apply, mvfderiv_clm_const (hL.mdifferentiableAt (by simp)), hBd, hp] at hd
    have h1 := hPair x hxO (C u) v
    have h2 := hPair x hxO u (C v)
    change B x (L x (C u)) v = _ at h1
    change B x (L x u) (C v) = _ at h2
    rw [hC] at h1 h2
    simp only [N, ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_add, map_sub]
    change B x (dL u) v - B x (L x (C u)) v + B x (C (L x u)) v = _
    change B x (dL u) v + (B x (C (L x u)) v + B x (L x u) (C v)) = _ at hd
    linarith only [hd, h1, h2]
  have htrN : LinearMap.trace ℝ E N.toLinearMap = LinearMap.trace ℝ E dL.toLinearMap := by
    change LinearMap.trace ℝ E
      (dL.toLinearMap - (L x).toLinearMap.comp C.toLinearMap +
        C.toLinearMap.comp (L x).toLinearMap) = _
    rw [map_add, map_sub, LinearMap.trace_comp_comm' C.toLinearMap (L x).toLinearMap]
    ring
  let e' := (e.continuousLinearEquivAt ℝ x hxe).symm
  let K := e'.toLinearEquiv.conj N.toLinearMap
  have hSe (v : E) : S x v = e' v :=
    (congrFun (e.symm_continuousLinearEquivAt_eq hxe) v).symm
  have hK (a b : TangentSpace (𝓡 n) x) : g.inner x (K a) b =
      D.covariantTensorDerivative T x
        (Fin.cons (A x) (Fin.append (fun i ↦ V i x) ![a, b])) +
      ∑ j, T x (Fin.append
        (Function.update (fun i ↦ V i x) j (D.connection (V j) x (A x))) ![a, b]) := by
    have hh := hN (e'.symm a) (e'.symm b)
    change g.inner x (S x (N (e'.symm a))) (S x (e'.symm b)) = _ at hh
    simp only [hSe, e'.apply_symm_apply] at hh
    exact hh
  have htraceValue : LinearMap.trace ℝ E dL.toLinearMap =
      tensorTraceLast g (D.covariantTensorDerivative T) x
        (Fin.cons (A x) (fun i ↦ V i x)) +
      ∑ j, tensorTraceLast g T x
        (Function.update (fun i ↦ V i x) j (D.connection (V j) x (A x))) := by
    rw [← htrN, ← LinearMap.trace_conj' N.toLinearMap e'.toLinearEquiv]
    change LinearMap.trace ℝ (TangentSpace (𝓡 n) x) K = _
    have htrace : LinearMap.trace ℝ (TangentSpace (𝓡 n) x) K =
        ∑ i, inner ℝ (g.orthonormalBasis x i) (K (g.orthonormalBasis x i)) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ (g.orthonormalBasis x).toBasis]
      simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply]
    rw [htrace]
    have hi (i) : inner ℝ (g.orthonormalBasis x i) (K (g.orthonormalBasis x i)) =
        g.inner x (K (g.orthonormalBasis x i)) (g.orthonormalBasis x i) :=
      g.symm x _ _
    simp only [hi, hK, Finset.sum_add_distrib, tensorTraceLast]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      simpa only [Fin.cast_refl, Function.comp_id] using
        (Fin.append_cons (A x) (fun j ↦ V j x)
          ![g.orthonormalBasis x i, g.orthonormalBasis x i]).symm
    · exact Finset.sum_comm
  let tr : (E →L[ℝ] E) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ))
  have htrdiff : mvfderiv (𝓡 n) (fun y ↦ tr (L y)) x (A x) = tr dL := by
    simpa only [mvfderiv_const, zero_apply, add_zero] using!
      mvfderiv_clm_apply (mdifferentiableAt_const (c := tr))
        (hL.mdifferentiableAt (by simp)) (A x)
  have hloc : (fun y ↦ tensorTraceLast g T y (fun i ↦ V i y)) =ᶠ[𝓝 x]
      (fun y ↦ tr (L y)) := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    exact (hTrace y hy).symm
  have hd : mvfderiv (𝓡 n) (fun y ↦ tensorTraceLast g T y (fun i ↦ V i y)) x =
      mvfderiv (𝓡 n) (fun y ↦ tr (L y)) x := hloc.mfderiv_eq
  rw [hd, htrdiff]
  exact htraceValue

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivative_tensorTraceLast {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (tensorTraceLast g T) x v =
      tensorTraceLast g (D.covariantTensorDerivative T) x v := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let A := FiberBundle.extend E (v 0)
  let V (i : Fin k) := FiberBundle.extend E (v i.succ)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% A) e.baseSet :=
    contMDiffOn_extend_baseSet (v 0)
  have hV (i : Fin k) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E))
      ∞ (T% (V i)) e.baseSet := contMDiffOn_extend_baseSet (v i.succ)
  have h1 := tensor_trace_product_rule D hT e.open_baseSet hA hV hx
  have h2 := tensor_product_rule D (isSmoothCovariantTensor_tensorTraceLast g hT)
    e.open_baseSet hA hV hx
  have he : Fin.cons (A x) (fun i ↦ V i x) = v := by
    funext i
    cases i using Fin.cases <;> simp only [Fin.cons_zero, Fin.cons_succ, A, V,
      FiberBundle.extend_apply_self]
  rw [he] at h1 h2
  exact add_right_cancel (h2.symm.trans h1)

set_option backward.isDefEq.respectTransparency false in
theorem tensorLaplacian_tensorTraceLast {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T)
    (x : M) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.tensorLaplacian (tensorTraceLast g T) x v =
      tensorTraceLast g (D.tensorLaplacian T) x v := by
  classical
  have h1 : D.covariantTensorDerivative (tensorTraceLast g T) =
      tensorTraceLast g (D.covariantTensorDerivative T) := by
    funext y w
    exact covariantTensorDerivative_tensorTraceLast D hT y w
  have h2 (w : Fin (k + 2) → TangentSpace (𝓡 n) x) :
      D.iteratedCovariantTensorDerivative (tensorTraceLast g T) 2 x w =
        tensorTraceLast g (D.iteratedCovariantTensorDerivative T 2) x w := by
    simp only [LeviCivitaData.iteratedCovariantTensorDerivative, h1]
    exact covariantTensorDerivative_tensorTraceLast D
      (isSmoothCovariantTensor_covariantTensorDerivative D hT) x w
  simp only [LeviCivitaData.tensorLaplacian, h2, tensorTraceLast]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Fin.append_cons, Fin.cast_refl, Function.comp_id]

end PoincareConjecture.M04

