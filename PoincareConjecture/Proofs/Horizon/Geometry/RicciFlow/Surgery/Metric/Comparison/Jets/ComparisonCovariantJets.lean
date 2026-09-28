import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderAllOrder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderPlaneBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactEnergy
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.MetricSurgery

open CoordinateExponential

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable def comparisonTensorComponent {k : ℕ}
    (T : CovariantTensorEvaluation 3 E k) (a : Fin k → Fin 3) (x : E) : ℝ :=
  T x (fun i => e (a i))

noncomputable def comparisonChristoffel (g : RiemannianMetric 3 E)
    (a b c : Fin 3) (x : E) : ℝ :=
  inner ℝ (e a) (christoffelBilinear g.euclideanCoefficients x (e b) (e c))

theorem comparisonChristoffel_contDiff (g : RiemannianMetric 3 E)
    (a b c : Fin 3) : ContDiff ℝ ∞ (comparisonChristoffel g a b c) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact contDiffAt_const.inner ℝ
    (((contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
      (g.inner_isInvertible x)).clm_apply contDiffAt_const).clm_apply contDiffAt_const)

theorem comparisonTensorComponent_contDiff {k : ℕ}
    {T : CovariantTensorEvaluation 3 E k} (hT : IsSmoothCovariantTensor T)
    (a : Fin k → Fin 3) : ContDiff ℝ ∞ (comparisonTensorComponent T a) := by
  have hc := hT.2 Set.univ isOpen_univ (fun i _ => e (a i)) (fun i => by
    apply contMDiffOn_univ.mpr
    intro y
    rw [Bundle.contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := e (a i))⟩)
  exact contMDiff_iff_contDiff.mp (contMDiffOn_univ.mp hc)


theorem comparisonTensorComponent_covariant {g : RiemannianMetric 3 E}
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation 3 E k}
    (hT : IsSmoothCovariantTensor T) (a : Fin (k + 1) → Fin 3) (x : E) :
    comparisonTensorComponent (D.covariantTensorDerivative T) a x =
      fderiv ℝ (comparisonTensorComponent T (fun i => a i.succ)) x (e (a 0)) -
      ∑ i : Fin k, ∑ b : Fin 3,
        comparisonChristoffel g b (a 0) (a i.succ) x *
          comparisonTensorComponent T (Function.update (fun j => a j.succ) i b) x := by
  classical
  have h := D.fderiv_covariantTensor_pullback_model hT
    (q := id) (V := fun i _ => e (a i.succ)) (p := x)
    differentiableAt_id (fun i => differentiableAt_const (e (a i.succ))) (e (a 0))
  simp only [id_eq, fderiv_id, ContinuousLinearMap.id_apply,
    LeviCivitaData.manifoldCovDerivAlong_model, ConnectionVariation.covDerivAlong_def,
    fderiv_const_apply, zero_apply, zero_add] at h
  have htuple : Fin.cons (e (a 0)) (fun i => e (a i.succ)) = fun i => e (a i) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [htuple] at h
  change fderiv ℝ (comparisonTensorComponent T (fun i => a i.succ)) x (e (a 0)) =
    comparisonTensorComponent (D.covariantTensorDerivative T) a x + _ at h
  rw [eq_sub_iff_add_eq]
  convert h.symm using 2
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨A, hA⟩ := hT.1 x
  simp_rw [comparisonTensorComponent, hA]
  rw [← (e).sum_repr'
    (christoffelBilinear g.euclideanCoefficients x (e (a 0)) (e (a i.succ)))]
  rw [A.map_update_sum]
  simp only [A.map_update_smul, smul_eq_mul, comparisonChristoffel]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply congrArg A
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj]

theorem exists_comparisonChristoffel_jet_bound (g : RiemannianMetric 3 E)
    {K : Set E} (hK : IsCompact K) (j : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ a b c : Fin 3, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (comparisonChristoffel g a b c) x‖ ≤ G := by
  classical
  choose A hA using fun a b c : Fin 3 => hK.exists_bound_of_continuousOn
    ((ContDiff.continuous_iteratedFDeriv
      (m := j) (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
      (comparisonChristoffel_contDiff g a b c)).continuousOn)
  let G := 1 + ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, max (A a b c) 0
  have hsum : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, max (A a b c) 0 := by
    positivity
  refine ⟨G, by dsimp [G]; linarith only [hsum], ?_⟩
  intro a b c x hx
  apply (hA a b c x hx).trans
  refine (le_max_left (A a b c) 0).trans ?_
  have hc : max (A a b c) 0 ≤ ∑ c : Fin 3, max (A a b c) 0 :=
    Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ c)
  have hb : (∑ c : Fin 3, max (A a b c) 0) ≤
      ∑ b : Fin 3, ∑ c : Fin 3, max (A a b c) 0 :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _))
      (Finset.mem_univ b)
  have ha : (∑ b : Fin 3, ∑ c : Fin 3, max (A a b c) 0) ≤
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, max (A a b c) 0 :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => le_max_right _ _))) (Finset.mem_univ a)
  exact (hc.trans (hb.trans ha)).trans (by dsimp [G]; linarith)


theorem exists_comparisonTensorComponent_iterated_bound
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    {K : Set E} (hK : IsCompact K) (k j m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : CovariantTensorEvaluation 3 E k),
      IsSmoothCovariantTensor T → ∀ rho : ℝ, 0 ≤ rho → ∀ x ∈ K,
      (∀ l : ℕ, l ≤ j + m → ∀ a : Fin k → Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonTensorComponent T a) x‖ ≤ rho) →
      ∀ a : Fin (k + m) → Fin 3,
        ‖iteratedFDeriv ℝ j
          (comparisonTensorComponent (D.iteratedCovariantTensorDerivative T m) a) x‖ ≤
            C * rho := by
  classical
  induction m generalizing j with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro T hT rho hrho x hx hbase a
      simpa only [LeviCivitaData.iteratedCovariantTensorDerivative, one_mul] using
        hbase j (by omega) a
  | succ m ih =>
      obtain ⟨A, hA, hAbound⟩ := ih (j + 1)
      choose C hC hCbound using fun l : Fin (j + 1) => ih l
      choose G hG hGbound using fun l : Fin (j + 1) =>
        exists_comparisonChristoffel_jet_bound g hK l
      let D0 := 1 + ∑ l : Fin (j + 1), C l
      have hD0 : 0 < D0 := by
        have hsum : 0 ≤ ∑ l : Fin (j + 1), C l :=
          Finset.sum_nonneg (fun l _ => (hC l).le)
        dsimp [D0]
        linarith only [hsum]
      have hCle (l : Fin (j + 1)) : C l ≤ D0 := by
        have h := Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ l)
        dsimp [D0]
        linarith only [h]
      let S := ∑ l : Fin (j + 1), (j.choose l : ℝ) * G l * D0
      have hS : 0 ≤ S := by
        apply Finset.sum_nonneg
        intro l _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG l).le) hD0.le
      refine ⟨A + (k + m : ℕ) * 3 * S, by positivity, ?_⟩
      intro T hT rho hrho x hx hbase a
      let Tm := D.iteratedCovariantTensorDerivative T m
      have hTm : IsSmoothCovariantTensor Tm :=
        D.iteratedCovariantTensorDerivative_isSmooth hT m
      have hlow (l : ℕ) (hl : l ≤ j) (b : Fin (k + m) → Fin 3) :
          ‖iteratedFDeriv ℝ l (comparisonTensorComponent Tm b) x‖ ≤ D0 * rho := by
        let l' : Fin (j + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
        exact (hCbound l' T hT rho hrho x hx (fun s hs b => hbase s (by
          dsimp [l'] at hs
          omega) b) b).trans (mul_le_mul_of_nonneg_right (hCle l') hrho)
      have hproduct (b c d : Fin 3) (t : Fin (k + m) → Fin 3) :
          ‖iteratedFDeriv ℝ j (fun y => comparisonChristoffel g b c d y *
            comparisonTensorComponent Tm t y) x‖ ≤ S * rho := by
        have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt
          (x := x)
          (comparisonChristoffel_contDiff g b c d).contDiffAt
          (comparisonTensorComponent_contDiff hTm t).contDiffAt j
        simp only [smul_eq_mul] at h
        apply h.trans
        rw [← Fin.sum_univ_eq_sum_range]
        calc
          _ ≤ ∑ l : Fin (j + 1), (j.choose l : ℝ) * G l * (D0 * rho) := by
            apply Finset.sum_le_sum
            intro l _
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (hGbound l b c d x hx) (Nat.cast_nonneg _)
            · exact hlow (j - l) (Nat.sub_le _ _) t
            · exact norm_nonneg _
            · exact mul_nonneg (Nat.cast_nonneg _) (hG l).le
          _ = S * rho := by simp only [S, Finset.sum_mul, mul_assoc]
      have hderiv : ‖iteratedFDeriv ℝ j (fun y =>
          fderiv ℝ (comparisonTensorComponent Tm (fun i => a i.succ)) y (e (a 0))) x‖ ≤
            A * rho := by
        have h := norm_iteratedFDeriv_clm_apply_const (x := x)
          ((comparisonTensorComponent_contDiff hTm (fun i => a i.succ)).contDiffAt.fderiv_right
            (m := ∞) (by simp)) (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)
          (c := e (a 0))
        simp only [(e).norm_eq_one, one_mul, norm_iteratedFDeriv_fderiv] at h
        exact h.trans (hAbound T hT rho hrho x hx
          (fun s hs b => hbase s (by omega) b) _)
      let H (i : Fin (k + m)) (b : Fin 3) (y : E) :=
        comparisonChristoffel g b (a 0) (a i.succ) y *
          comparisonTensorComponent Tm (Function.update (fun l => a l.succ) i b) y
      have hH (i : Fin (k + m)) (b : Fin 3) : ContDiffAt ℝ ∞ (H i b) x :=
        (comparisonChristoffel_contDiff g b (a 0) (a i.succ)).contDiffAt.mul
          (comparisonTensorComponent_contDiff hTm _).contDiffAt
      have hsum : ‖iteratedFDeriv ℝ j (fun y => ∑ i, ∑ b, H i b y) x‖ ≤
          (k + m : ℕ) * 3 * S * rho := by
        calc
          _ ≤ ∑ i : Fin (k + m), ‖iteratedFDeriv ℝ j (fun y => ∑ b, H i b y) x‖ :=
            norm_iteratedFDeriv_finite_sum _ (fun i => ContDiffAt.sum (fun b _ => hH i b)) j
          _ ≤ ∑ i : Fin (k + m), ∑ b : Fin 3, ‖iteratedFDeriv ℝ j (H i b) x‖ :=
            Finset.sum_le_sum (fun i _ => norm_iteratedFDeriv_finite_sum _ (hH i) j)
          _ ≤ ∑ _i : Fin (k + m), ∑ _b : Fin 3, S * rho :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun b _ =>
              hproduct b (a 0) (a i.succ) _))
          _ = _ := by simp; ring
      have heq : comparisonTensorComponent (D.iteratedCovariantTensorDerivative T (m + 1)) a =
          fun y => fderiv ℝ (comparisonTensorComponent Tm (fun i => a i.succ)) y (e (a 0)) -
            ∑ i, ∑ b, H i b y :=
        funext (comparisonTensorComponent_covariant D hTm a)
      have hds : ContDiffAt ℝ ∞ (fun y =>
          fderiv ℝ (comparisonTensorComponent Tm (fun i => a i.succ)) y (e (a 0))) x :=
        ((comparisonTensorComponent_contDiff hTm _).contDiffAt.fderiv_right
          (m := ∞) (by simp)).clm_apply contDiffAt_const
      have hss : ContDiffAt ℝ ∞ (fun y => ∑ i, ∑ b, H i b y) x :=
        ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun b _ => hH i b))
      rw [heq, fun_iteratedFDeriv_sub_apply
        (hds.of_le (by exact_mod_cast le_top)) (hss.of_le (by exact_mod_cast le_top))]
      exact (norm_sub_le _ _).trans ((add_le_add hderiv hsum).trans_eq (by ring))


theorem comparison_covariantTensorDerivative_eventuallyEq
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) {k : ℕ}
    {T S : CovariantTensorEvaluation 3 E k} {x : E} (h : ∀ᶠ y in nhds x, T y = S y) :
    ∀ᶠ y in nhds x, D.covariantTensorDerivative T y = D.covariantTensorDerivative S y := by
  filter_upwards [h.eventually_nhds] with y hy
  funext v
  have heq : (fun z => T z (fun i => FiberBundle.extend E (v i.succ) z)) =ᶠ[nhds y]
      (fun z => S z (fun i => FiberBundle.extend E (v i.succ) z)) := by
    filter_upwards [hy] with z hz
    rw [hz]
  unfold LeviCivitaData.covariantTensorDerivative
  have hd : mvfderiv (𝓡 3)
      (fun z => T z (fun i => FiberBundle.extend E (v i.succ) z)) y =
      mvfderiv (𝓡 3) (fun z => S z (fun i => FiberBundle.extend E (v i.succ) z)) y :=
    heq.mfderiv_eq
  rw [hd, hy.self_of_nhds]

theorem comparison_iteratedCovariantTensorDerivative_eventuallyEq
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) {k : ℕ}
    {T S : CovariantTensorEvaluation 3 E k} {x : E} (h : ∀ᶠ y in nhds x, T y = S y) (m : ℕ) :
    ∀ᶠ y in nhds x, D.iteratedCovariantTensorDerivative T m y =
      D.iteratedCovariantTensorDerivative S m y := by
  induction m with
  | zero => exact h
  | succ m ih => exact comparison_covariantTensorDerivative_eventuallyEq D ih

theorem comparison_bilinear_isSmooth {B : E → Bilin} (hB : ContDiff ℝ ∞ B) :
    IsSmoothCovariantTensor (k := 2) (fun x v => B x (v 0) (v 1)) := by
  constructor
  · intro x
    refine ⟨{
      toFun := fun v => B x (v 0) (v 1)
      map_update_add' := ?_
      map_update_smul' := ?_ }, fun _ => rfl⟩
    · intro _ v i a b
      fin_cases i <;> simp [map_add]
    · intro _ v i c a
      fin_cases i <;> simp [map_smul, smul_apply]
  · intro U hU X hX x hx
    have hXi (i : Fin 2) : ContDiffAt ℝ ∞ (X i) x := by
      have h := (Bundle.contMDiffAt_totalSpace.mp ((hX i).contMDiffAt (hU.mem_nhds hx))).2
      simpa using contMDiffAt_iff_contDiffAt.mp h
    exact (contMDiffAt_iff_contDiffAt.mpr
      ((hB.contDiffAt.clm_apply (hXi 0)).clm_apply (hXi 1))).contMDiffWithinAt


theorem exists_comparison_smooth_germ {B : E → Bilin} {U : Set E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) {x : E} (hx : x ∈ U) :
    ∃ A : E → Bilin, ContDiff ℝ ∞ A ∧ A =ᶠ[nhds x] B := by
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let f : ContDiffBump x :=
    { rIn := d / 4
      rOut := d / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith only [hd] }
  have hsupp : tsupport f ⊆ U := by
    rw [f.tsupport_eq]
    intro y hy
    apply hball
    have hdist : dist y x ≤ d / 2 := hy
    exact hdist.trans_lt (half_lt_self hd)
  refine ⟨fun y => f y • B y, contDiff_iff_contDiffAt.mpr (fun y => ?_), ?_⟩
  · by_cases hy : y ∈ tsupport f
    · exact f.contDiff.contDiffAt.smul (hB.contDiffAt (hU.mem_nhds (hsupp hy)))
    · apply (contDiffAt_const (c := (0 : Bilin))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [hz]
  · filter_upwards [f.eventuallyEq_one] with y hy
    simp [hy]

theorem exists_comparison_unit_norm_bound (g : RiemannianMetric 3 E)
    {K : Set E} (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ K, ∀ v : E, g.inner x v v = 1 → ‖v‖ ≤ L := by
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound hK hg.continuous.continuousOn
    (fun x _ v hv => g.pos x v hv)
  refine ⟨1 + 1 / c, by positivity, ?_⟩
  intro x hx v hv
  have hsq : ‖v‖ ^ 2 ≤ 1 / c := by
    apply (le_div_iff₀ hc).mpr
    have h := hbound x hx v
    change c * ‖v‖ ^ 2 ≤ g.inner x v v at h
    nlinarith only [h, hv]
  nlinarith only [hsq, sq_nonneg (‖v‖ - 1 / 2)]

theorem comparison_tensor_evaluation_bound {k : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin k => E) ℝ) {rho L : ℝ}
    (hrho : 0 ≤ rho) (_hL : 0 ≤ L)
    (hA : ∀ a : Fin k → Fin 3, |A (fun i => e (a i))| ≤ rho)
    (v : Fin k → E) (hv : ∀ i, ‖v i‖ ≤ L) :
    |A v| ≤ (3 : ℝ) ^ k * L ^ k * rho := by
  have hprod : (∏ i, ‖v i‖) ≤ L ^ k := by
    calc
      _ ≤ ∏ _i : Fin k, L :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hv i)
      _ = _ := by simp
  exact (euclideanThree_multilinear_apply_bound A hrho hA v).trans
    ((mul_le_mul_of_nonneg_left hprod (mul_nonneg (by positivity) hrho)).trans_eq (by ring))

theorem exists_comparison_tensorNorm_bound (g : RiemannianMetric 3 E)
    {K : Set E} (hK : IsCompact K) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : CovariantTensorEvaluation 3 E k) (x : E), x ∈ K →
      (∃ A : MultilinearMap ℝ (fun _ : Fin k => E) ℝ, ∀ v, T x v = A v) →
      ∀ rho : ℝ, 0 ≤ rho →
      (∀ a : Fin k → Fin 3, |comparisonTensorComponent T a x| ≤ rho) →
        g.tensorNorm T x ≤ C * rho := by
  classical
  obtain ⟨L, hL, hLbound⟩ := exists_comparison_unit_norm_bound g hK
  let A0 := (3 : ℝ) ^ k * L ^ k
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  refine ⟨Real.sqrt ((3 : ℝ) ^ k) * A0, by positivity, ?_⟩
  intro T x hx hT rho hrho hcoeff
  obtain ⟨A, hA⟩ := hT
  let b := g.orthonormalBasis x
  have hunit (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      g.inner x (b i) (b i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hcomponent (a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      |T x (fun i => b (a i))| ≤ A0 * rho := by
    rw [hA]
    exact comparison_tensor_evaluation_bound A hrho hL.le
      (fun c => by simpa only [comparisonTensorComponent, hA] using hcoeff c)
      _ (fun i => hLbound x hx _ (hunit (a i)))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    simp [TangentSpace]
  have hsq : (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
      (T x (fun i => b (a i))) ^ 2) ≤ (3 : ℝ) ^ k * (A0 * rho) ^ 2 := by
    calc
      _ ≤ ∑ _a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          (A0 * rho) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [← pow_two, sq_abs] using
          (mul_self_le_mul_self (abs_nonneg _) (hcomponent a))
      _ = _ := by simp [hdim]
  change Real.sqrt _ ≤ _
  apply (Real.sqrt_le_sqrt hsq).trans_eq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (mul_nonneg hA0.le hrho)]
  ring

theorem exists_comparisonTensor_iterated_norm_bound
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    {K : Set E} (hK : IsCompact K) (k m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : CovariantTensorEvaluation 3 E k),
      IsSmoothCovariantTensor T → ∀ rho : ℝ, 0 ≤ rho → ∀ x ∈ K,
      (∀ l : ℕ, l ≤ m → ∀ a : Fin k → Fin 3,
        ‖iteratedFDeriv ℝ l (comparisonTensorComponent T a) x‖ ≤ rho) →
      g.tensorNorm (D.iteratedCovariantTensorDerivative T m) x ≤ C * rho := by
  obtain ⟨A, hA, hAbound⟩ := exists_comparisonTensorComponent_iterated_bound D hK k 0 m
  obtain ⟨B, hB, hBbound⟩ := exists_comparison_tensorNorm_bound g hK (k + m)
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  intro T hT rho hrho x hx hbase
  have hTm := D.iteratedCovariantTensorDerivative_isSmooth hT m
  have hc (a : Fin (k + m) → Fin 3) :
      |comparisonTensorComponent (D.iteratedCovariantTensorDerivative T m) a x| ≤ A * rho := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      hAbound T hT rho hrho x hx (by simpa only [zero_add] using hbase) a
  simpa only [mul_assoc] using hBbound _ x hx (hTm.1 x) (A * rho) (mul_nonneg hA.le hrho) hc



theorem exists_comparison_covariant_jet_bound
    (g : RiemannianMetric 3 E) (D : LeviCivitaData g)
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set E), IsOpen U → K ⊆ U →
      ∀ (B : E → Bilin), ContDiffOn ℝ ∞ B U → ∀ rho : ℝ, 0 ≤ rho →
      ∀ x ∈ K,
      (∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j (B - g.euclideanCoefficients) x‖ ≤ rho) →
      singularMetricJetErrorSquared g D (fun y v => B y (v 0) (v 1)) m x ≤ C * rho ^ 2 := by
  classical
  choose A hA hAbound using fun j : Fin (m + 1) =>
    exists_comparisonTensor_iterated_norm_bound D hK 2 j
  let C := 1 + ∑ j : Fin (m + 1), (A j) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro U hU hKU B hB rho hrho x hx hbase
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  obtain ⟨F, hF, heq⟩ := exists_comparison_smooth_germ hU (hB.sub hg.contDiffOn) (hKU hx)
  let T : CovariantTensorEvaluation 3 E 2 := fun y v => F y (v 0) (v 1)
  have hT : IsSmoothCovariantTensor T := comparison_bilinear_isSmooth hF
  have hcoeff (j : ℕ) (hj : j ≤ m) (a : Fin 2 → Fin 3) :
      ‖iteratedFDeriv ℝ j (comparisonTensorComponent T a) x‖ ≤ rho := by
    have h1 := norm_iteratedFDeriv_clm_apply_const (hF.contDiffAt (x := x))
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (c := e (a 0))
    have h2 := norm_iteratedFDeriv_clm_apply_const
      (((hF.contDiffAt (x := x)).clm_apply (contDiffAt_const (c := e (a 0)))))
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top) (c := e (a 1))
    simp only [(e).norm_eq_one, one_mul] at h1 h2
    apply (h2.trans h1).trans
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    exact hbase j hj
  have hTeq : ∀ᶠ y in nhds x,
      T y = (fun v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) := by
    filter_upwards [heq] with y hy
    funext v
    change F y (v 0) (v 1) = _
    rw [hy]
    rfl
  have hbound (j : Fin (m + 1)) :
      g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) j) x ≤ A j * rho := by
    have hn : g.tensorNorm (D.iteratedCovariantTensorDerivative T j) x =
        g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
          (fun y v => B y (v 0) (v 1) - g.inner y (v 0) (v 1)) j) x := by
      unfold RiemannianMetric.tensorNorm
      rw [(comparison_iteratedCovariantTensorDerivative_eventuallyEq D hTeq j).self_of_nhds]
    rw [← hn]
    exact hAbound j T hT rho hrho x hx (fun l hl a => hcoeff l (by omega) a)
  unfold singularMetricJetErrorSquared
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ ≤ ∑ j : Fin (m + 1), (A j * rho) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply (sq_le_sq₀ (by unfold RiemannianMetric.tensorNorm; positivity)
        (mul_nonneg (hA j).le hrho)).mpr
      exact hbound j
    _ = (∑ j : Fin (m + 1), (A j) ^ 2) * rho ^ 2 := by
      simp only [mul_pow, Finset.sum_mul]
    _ ≤ C * rho ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg rho)
      dsimp [C]
      linarith

end PoincareConjecture.MetricSurgery
