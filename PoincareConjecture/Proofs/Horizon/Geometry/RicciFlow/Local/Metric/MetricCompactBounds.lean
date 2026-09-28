import PoincareConjecture.Proofs.M03.MetricCompactBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Connection.Family
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz






















set_option autoImplicit false
set_option maxHeartbeats 5000000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set Filter

universe u

namespace PoincareConjecture.RicciFlow.Local

theorem exists_pos_uniform_bilinear_bounds
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {K : Set X}
    (hK : IsCompact K) (hB : ContinuousOn B K)
    (hpos : ∀ x ∈ K, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ B x v v ∧ B x v v ≤ C * ‖v‖ ^ 2 := by
  let S := K ×ˢ Metric.sphere (0 : E) 1
  let f : X × E → ℝ := fun p => B p.1 p.2 p.2
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hf : ContinuousOn f S :=
    ((hB.comp continuousOn_fst (fun _ hp => hp.1)).clm_apply
      continuousOn_snd).clm_apply continuousOn_snd
  have hposS (p : X × E) (hp : p ∈ S) : 0 < f p := by
    apply hpos p.1 hp.1 p.2
    intro hz
    have hn := Metric.mem_sphere.mp hp.2
    simp [hz] at hn
  obtain ⟨c, hc, hcl⟩ := hS.exists_forall_le' hf hposS
  obtain ⟨C₀, hC₀⟩ := hS.bddAbove_image hf
  refine ⟨c, max C₀ 1, hc, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : E) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ hn]
  have hvw : ‖v‖ • w = v := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hscale : B x v v = ‖v‖ ^ 2 * f (x, w) := by
    calc
      B x v v = B x (‖v‖ • w) (‖v‖ • w) := by rw [hvw]
      _ = ‖v‖ ^ 2 * f (x, w) := by
        simp only [map_smul, smul_apply, smul_eq_mul]
        dsimp [f]
        ring
  constructor
  · calc
      c * ‖v‖ ^ 2 = ‖v‖ ^ 2 * c := mul_comm _ _
      _ ≤ ‖v‖ ^ 2 * f (x, w) :=
        mul_le_mul_of_nonneg_left (hcl (x, w) ⟨hx, hw⟩) (sq_nonneg _)
      _ = B x v v := hscale.symm
  · calc
      B x v v = ‖v‖ ^ 2 * f (x, w) := hscale
      _ ≤ ‖v‖ ^ 2 * C₀ := mul_le_mul_of_nonneg_left
        (hC₀ (Set.mem_image_of_mem f ⟨hx, hw⟩)) (sq_nonneg _)
      _ ≤ ‖v‖ ^ 2 * max C₀ 1 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
      _ = max C₀ 1 * ‖v‖ ^ 2 := mul_comm _ _

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_pos_uniform_metric_frame_bounds
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (hJ : IsCompact J)
    (x₀ : M) {K : Set M} (hK : IsCompact K)
    (hKchart : K ⊆ (trivializationAt
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀).baseSet) :
    let e := trivializationAt
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t ∈ J, ∀ x ∈ K,
      ∀ v : EuclideanSpace ℝ (Fin n),
        c * ‖v‖ ^ 2 ≤ (g t).inner x (e.symmL ℝ x v) (e.symmL ℝ x v) ∧
        (g t).inner x (e.symmL ℝ x v) (e.symmL ℝ x v) ≤ C * ‖v‖ ^ 2 := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x₀
  let frame (a : EuclideanSpace ℝ (Fin n)) (x : M) : TangentSpace (𝓡 n) x :=
    e.symmL ℝ x a
  have hframe (a : EuclideanSpace ℝ (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (frame a)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := a)).congr ?_
    intro x hx
    simpa [frame, Trivialization.symmL_apply _ hx] using
      congrArg Prod.snd (e.apply_mk_symm hx a)
  let G (q : ℝ × M) : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ) x₀ q.2 x₀ q.2 ((g q.1).inner q.2)
  have heval (q : ℝ × M) (hq : q.2 ∈ e.baseSet)
      (a b : EuclideanSpace ℝ (Fin n)) :
      G q a b = (g q.1).inner q.2 (frame a q.2) (frame b q.2) := by
    dsimp [G]
    rw [inCoordinates_apply_eq₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hq hq (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hq a,
      ← Trivialization.symmL_apply (R := ℝ) e hq b]
    simp [frame]
  have hG : ContinuousOn G (J ×ˢ e.baseSet) := by
    apply continuousOn_clm_apply.mpr
    intro a
    apply continuousOn_clm_apply.mpr
    intro b
    apply (contMDiffOn_family_metric_pair hg (frame a) (frame b)
      (hframe a) (hframe b)).continuousOn.congr
    intro q hq
    exact heval q hq.2 a b
  have hG' : ContinuousOn G (J ×ˢ K) :=
    hG.mono (Set.prod_mono subset_rfl hKchart)
  have hposG (q : ℝ × M) (hq : q ∈ J ×ˢ K)
      (a : EuclideanSpace ℝ (Fin n)) (ha : a ≠ 0) : 0 < G q a a := by
    rw [heval q (hKchart hq.2) a a]
    apply (g q.1).pos q.2
    intro hz
    have heq := congrArg (e.continuousLinearMapAt ℝ q.2) hz
    change e.continuousLinearMapAt ℝ q.2 (e.symmL ℝ q.2 a) =
      e.continuousLinearMapAt ℝ q.2 0 at heq
    rw [Trivialization.continuousLinearMapAt_symmL _ (hKchart hq.2), map_zero] at heq
    exact ha heq
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    exists_pos_uniform_bilinear_bounds (hJ.prod hK) hG' hposG
  refine ⟨c, C, hc, hC, ?_⟩
  intro t ht x hx v
  change c * ‖v‖ ^ 2 ≤ (g t).inner x (frame v x) (frame v x) ∧
    (g t).inner x (frame v x) (frame v x) ≤ C * ‖v‖ ^ 2
  rw [← heval (t, x) (hKchart hx) v v]
  exact hbounds (t, x) ⟨ht, hx⟩ v

theorem abs_ricci_le_curvatureTensorNorm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    |D.ricci x u v| ≤ (n : ℝ) * D.curvatureTensorNorm x *
      g.tangentNorm x u * g.tangentNorm x v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  obtain ⟨R, hR⟩ := exists_curvature_trilinearMap D x
  let r (p i q j : ι) := D.curvatureTensor x (b p) (b i) (b q) (b j)
  let N := ∑ p : ι, ∑ i : ι, ∑ q : ι, ∑ j : ι, r p i q j ^ 2
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hNnorm : D.curvatureTensorNorm x ^ 2 = N := Real.sq_sqrt hN
  have hnorm0 : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  have hpair (w : TangentSpace (𝓡 n) x) : g.inner x w w = ‖w‖ ^ 2 :=
    real_inner_self_eq_norm_sq w
  have hnorm (w : TangentSpace (𝓡 n) x) : g.tangentNorm x w = ‖w‖ := by
    rw [RiemannianMetric.tangentNorm, hpair, Real.sqrt_sq (norm_nonneg _)]
  have hrepr (w : TangentSpace (𝓡 n) x) :
      ∑ p : ι, (b.repr w p) ^ 2 = ‖w‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_inner_right w
  have hexpand (i : ι) : D.curvatureTensor x u (b i) v (b i) =
      ∑ p : ι, ∑ q : ι, (b.repr u p * b.repr v q) * r p i q i := by
    change g.inner x (D.curvature x u (b i) (b i)) v = _
    rw [← hR]
    nth_rw 1 [← b.sum_repr u, ← b.sum_repr v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    dsimp only [r, LeviCivitaData.curvatureTensor]
    rw [hR]
    ring
  have hslice (i : ι) : (∑ pq : ι × ι, r pq.1 i pq.2 i ^ 2) ≤ N := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro p _
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
        show 0 ≤ ∑ q : ι, ∑ k : ι, r p j q k ^ 2 by positivity)
      (Finset.mem_univ i)
    apply le_trans _ hi
    apply Finset.sum_le_sum
    intro q _
    exact Finset.single_le_sum (fun k _ => sq_nonneg (r p i q k)) (Finset.mem_univ i)
  have hweight : (∑ pq : ι × ι, (b.repr u pq.1 * b.repr v pq.2) ^ 2) =
      ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hrepr, hrepr]
  have hterm (i : ι) : |D.curvatureTensor x u (b i) v (b i)| ≤
      D.curvatureTensorNorm x * ‖u‖ * ‖v‖ := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι))
      (fun pq => b.repr u pq.1 * b.repr v pq.2) (fun pq => r pq.1 i pq.2 i)
    rw [hweight] at hcs
    have hle := mul_le_mul_of_nonneg_left (hslice i) (by positivity : 0 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2)
    have hsquare : D.curvatureTensor x u (b i) v (b i) ^ 2 ≤
        (D.curvatureTensorNorm x * ‖u‖ * ‖v‖) ^ 2 := by
      rw [hexpand]
      rw [Fintype.sum_prod_type] at hcs
      calc
        _ ≤ (‖u‖ ^ 2 * ‖v‖ ^ 2) * N := hcs.trans hle
        _ = _ := by rw [mul_pow, mul_pow, hNnorm]; ring
    have hright : 0 ≤ D.curvatureTensorNorm x * ‖u‖ * ‖v‖ := by positivity
    nlinarith only [hsquare, sq_abs (D.curvatureTensor x u (b i) v (b i)),
      abs_nonneg (D.curvatureTensor x u (b i) v (b i)), hright]
  have hdim : Fintype.card ι = n := by
    simp only [ι, Fintype.card_fin]
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x, finrank_euclideanSpace_fin]
  calc
    |D.ricci x u v| = |∑ i : ι, D.curvatureTensor x u (b i) v (b i)| := rfl
    _ ≤ ∑ i : ι, |D.curvatureTensor x u (b i) v (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, D.curvatureTensorNorm x * ‖u‖ * ‖v‖ :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hdim, nsmul_eq_mul, hnorm]; ring

theorem metric_endpoint_control_of_curvature_bound
    {T C : ℝ} (hT : 0 < T) (F : RicciFlow n M (Set.Ico 0 T))
    (hRm : ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ C) :
    let a : ℝ := 2 * (n : ℝ) * max C 0
    (∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      Real.exp (-(a * T)) * (F.metric 0).inner x v v ≤ (F.metric t).inner x v v ∧
      (F.metric t).inner x v v ≤ Real.exp (a * T) * (F.metric 0).inner x v v) ∧
    ∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
      (∀ s ∈ Set.Ico 0 T, ∀ t ∈ Set.Ico 0 T,
        |(F.metric t).inner x u v - (F.metric s).inner x u v| ≤
          a * Real.exp (a * T) * |t - s| *
            (F.metric 0).tangentNorm x u * (F.metric 0).tangentNorm x v) ∧
      ∃ L : ℝ,
        Filter.Tendsto (fun t => (F.metric t).inner x u v) (𝓝[Set.Iio T] T) (𝓝 L) ∧
        ∀ t ∈ Set.Ico 0 T,
          |(F.metric t).inner x u v - L| ≤
            a * Real.exp (a * T) * (T - t) *
              (F.metric 0).tangentNorm x u * (F.metric 0).tangentNorm x v := by
  let a : ℝ := 2 * (n : ℝ) * max C 0
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have h0 : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_rfl, hT⟩
  have hnonneg (g : RiemannianMetric n M) (x : M)
      (w : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact le_of_lt (g.pos x w hw)
  have hnorm_nonneg (g : RiemannianMetric n M) (x : M)
      (w : TangentSpace (𝓡 n) x) : 0 ≤ g.tangentNorm x w := Real.sqrt_nonneg _
  have hrate (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M)
      (u v : TangentSpace (𝓡 n) x) :
      |-2 * (F.connection t).ricci x u v| ≤
        a * (F.metric t).tangentNorm x u * (F.metric t).tangentNorm x v := by
    have hu := hnorm_nonneg (F.metric t) x u
    have hv := hnorm_nonneg (F.metric t) x v
    calc
      _ = 2 * |(F.connection t).ricci x u v| := by rw [abs_mul]; norm_num
      _ ≤ 2 * ((n : ℝ) * (F.connection t).curvatureTensorNorm x *
          (F.metric t).tangentNorm x u * (F.metric t).tangentNorm x v) :=
        mul_le_mul_of_nonneg_left (abs_ricci_le_curvatureTensorNorm _ x u v) (by norm_num)
      _ = (2 * (n : ℝ) * (F.connection t).curvatureTensorNorm x) *
          (F.metric t).tangentNorm x u * (F.metric t).tangentNorm x v := by ring
      _ ≤ _ := by
        dsimp only [a]
        gcongr
        exact (hRm t ht x).trans (le_max_left _ _)
  have hdiag (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M)
      (w : TangentSpace (𝓡 n) x) :
      Real.exp (-(a * T)) * (F.metric 0).inner x w w ≤ (F.metric t).inner x w w ∧
      (F.metric t).inner x w w ≤ Real.exp (a * T) * (F.metric 0).inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    have hp (s : ℝ) : 0 < (F.metric s).inner x w w := (F.metric s).pos x w hw
    have hlrate (s : ℝ) (hs : s ∈ Set.Ico 0 T) :
        ‖(-2 * (F.connection s).ricci x w w) / (F.metric s).inner x w w‖ ≤ a := by
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hp s)]
      apply (div_le_iff₀ (hp s)).2
      calc
        _ ≤ a * (F.metric s).tangentNorm x w * (F.metric s).tangentNorm x w := hrate s hs x w w
        _ = a * ((F.metric s).tangentNorm x w) ^ 2 := by ring
        _ = _ := by rw [RiemannianMetric.tangentNorm, Real.sq_sqrt (hp s).le]
    have hl := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (F.equation s hs x w w).log (ne_of_gt (hp s))) hlrate
      (convex_Ico 0 T) h0 ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hl
    have hlog := abs_le.mp hl
    have hat : a * t ≤ a * T := mul_le_mul_of_nonneg_left ht.2.le ha
    constructor
    · have hh : -(a * T) + Real.log ((F.metric 0).inner x w w) ≤
          Real.log ((F.metric t).inner x w w) := by linarith [hlog.1, hat]
      simpa only [Real.exp_add, Real.exp_log (hp 0), Real.exp_log (hp t)] using Real.exp_le_exp.mpr hh
    · have hh : Real.log ((F.metric t).inner x w w) ≤
          a * T + Real.log ((F.metric 0).inner x w w) := by linarith [hlog.2, hat]
      simpa only [Real.exp_add, Real.exp_log (hp 0), Real.exp_log (hp t)] using Real.exp_le_exp.mpr hh
  refine ⟨hdiag, ?_⟩
  intro x u v
  let A := Real.exp (a * T)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hnorm_bound (t : ℝ) (ht : t ∈ Set.Ico 0 T) (w : TangentSpace (𝓡 n) x) :
      (F.metric t).tangentNorm x w ≤ Real.sqrt A * (F.metric 0).tangentNorm x w := by
    dsimp only [RiemannianMetric.tangentNorm]
    have hs := Real.sqrt_le_sqrt (hdiag t ht x w).2
    rw [Real.sqrt_mul hA] at hs
    exact hs
  have hprod (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
      (F.metric t).tangentNorm x u * (F.metric t).tangentNorm x v ≤
        A * (F.metric 0).tangentNorm x u * (F.metric 0).tangentNorm x v := by
    calc
      _ ≤ (Real.sqrt A * (F.metric 0).tangentNorm x u) *
          (Real.sqrt A * (F.metric 0).tangentNorm x v) :=
        mul_le_mul (hnorm_bound t ht u) (hnorm_bound t ht v)
          (hnorm_nonneg _ _ _) (mul_nonneg (Real.sqrt_nonneg _) (hnorm_nonneg _ _ _))
      _ = (Real.sqrt A) ^ 2 * (F.metric 0).tangentNorm x u *
          (F.metric 0).tangentNorm x v := by ring
      _ = _ := by rw [Real.sq_sqrt hA]
  let K : ℝ := a * A * (F.metric 0).tangentNorm x u * (F.metric 0).tangentNorm x v
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (mul_nonneg ha hA)
    (hnorm_nonneg _ _ _)) (hnorm_nonneg _ _ _)
  have hbound (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
      ‖-2 * (F.connection t).ricci x u v‖ ≤ K := by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ a * (F.metric t).tangentNorm x u * (F.metric t).tangentNorm x v := hrate t ht x u v
      _ ≤ K := by
        dsimp only [K]
        nlinarith only [mul_le_mul_of_nonneg_left (hprod t ht) ha]
  have hLip : LipschitzOnWith ⟨K, hK⟩ (fun t => (F.metric t).inner x u v) (Set.Ico 0 T) :=
    (convex_Ico 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => F.equation t ht x u v) (fun t ht => hbound t ht)
  constructor
  · intro s hs t ht
    have hh := hLip.dist_le_mul s hs t ht
    change |(F.metric s).inner x u v - (F.metric t).inner x u v| ≤ K * dist s t at hh
    rw [Real.dist_eq, abs_sub_comm] at hh
    have htime : |s - t| = |t - s| := abs_sub_comm _ _
    rw [htime] at hh
    calc
      _ ≤ K * |t - s| := hh
      _ = a * A * |t - s| * (F.metric 0).tangentNorm x u *
          (F.metric 0).tangentNorm x v := by dsimp only [K]; ring
  · obtain ⟨f, hf, heq⟩ := hLip.extend_real
    refine ⟨f T, ?_, ?_⟩
    · have hevent : ∀ᶠ t in 𝓝[Set.Iio T] T, t ∈ Set.Ico 0 T := by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht hpos
        exact ⟨hpos.le, ht⟩
      apply (hf.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [hevent] with t ht
      exact (heq ht).symm
    · intro t ht
      have hh := hf.dist_le_mul t T
      rw [← heq ht] at hh
      change |(F.metric t).inner x u v - f T| ≤ K * dist t T at hh
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le), neg_sub] at hh
      calc
        _ ≤ K * (T - t) := hh
        _ = a * A * (T - t) * (F.metric 0).tangentNorm x u *
            (F.metric 0).tangentNorm x v := by dsimp only [K]; ring

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_tangentNorm_le_curvatureTensorNorm
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    g.tangentNorm x (D.curvature x u v w) ≤
      D.curvatureTensorNorm x * g.tangentNorm x u *
        g.tangentNorm x v * g.tangentNorm x w := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  obtain ⟨R, hR⟩ := exists_curvature_trilinearMap D x
  let rb := fun γ : ι × ι × ι => R (b γ.1) (b γ.2.1) (b γ.2.2)
  let c := fun γ : ι × ι × ι =>
    b.repr u γ.1 * b.repr v γ.2.1 * b.repr w γ.2.2
  let N := ∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
    D.curvatureTensor x (b i) (b j) (b k) (b l) ^ 2
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hNnorm : D.curvatureTensorNorm x ^ 2 = N := Real.sq_sqrt hN
  have hnorm0 : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  have hnorm (z : TangentSpace (𝓡 n) x) : g.tangentNorm x z = ‖z‖ := by
    rw [RiemannianMetric.tangentNorm, show g.inner x z z = ‖z‖ ^ 2 from
      real_inner_self_eq_norm_sq z, Real.sqrt_sq (norm_nonneg _)]
  have hrepr (z : TangentSpace (𝓡 n) x) :
      ∑ i : ι, b.repr z i ^ 2 = ‖z‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_sq_inner_right z
  have houtput (i j k : ι) : ‖R (b i) (b j) (b k)‖ ^ 2 =
      ∑ l : ι, D.curvatureTensor x (b i) (b j) (b l) (b k) ^ 2 := by
    have hh := (b.sum_sq_inner_left (R (b i) (b j) (b k))).symm
    change ‖R (b i) (b j) (b k)‖ ^ 2 =
      ∑ l : ι, g.inner x (R (b i) (b j) (b k)) (b l) ^ 2 at hh
    simpa only [LeviCivitaData.curvatureTensor, ← hR] using hh
  have hEnergy : (∑ γ : ι × ι × ι, ‖rb γ‖ ^ 2) =
      D.curvatureTensorNorm x ^ 2 := by
    rw [hNnorm]
    simp only [Fintype.sum_prod_type, rb]
    dsimp only [N]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [houtput]
    exact Finset.sum_comm
  have hExpand : R u v w = ∑ γ : ι × ι × ι, c γ • rb γ := by
    dsimp only [c, rb]
    simp only [Fintype.sum_prod_type]
    nth_rw 1 [← b.sum_repr u]
    nth_rw 1 [← b.sum_repr v]
    nth_rw 1 [← b.sum_repr w]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.smul_sum, smul_smul, mul_assoc]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ring
  let H := ‖u‖ * ‖v‖ * ‖w‖
  have hweight : (∑ γ : ι × ι × ι, |c γ| ^ 2) = H ^ 2 := by
    calc
      _ = ∑ i : ι, ∑ j : ι, ∑ k : ι,
          b.repr u i ^ 2 * b.repr v j ^ 2 * b.repr w k ^ 2 := by
        simp only [c, sq_abs, Fintype.sum_prod_type, mul_pow]
      _ = (∑ i : ι, b.repr u i ^ 2) * (∑ j : ι, b.repr v j ^ 2) *
          (∑ k : ι, b.repr w k ^ 2) := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = H ^ 2 := by rw [hrepr, hrepr, hrepr]; dsimp only [H]; ring
  let S := ∑ γ : ι × ι × ι, |c γ| * ‖rb γ‖
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι × ι))
    (fun γ => |c γ|) (fun γ => ‖rb γ‖)
  change S ^ 2 ≤ _ at hcs
  rw [hweight, hEnergy] at hcs
  have hbound : S ≤ D.curvatureTensorNorm x * H := by
    have hS0 : 0 ≤ S := by dsimp only [S]; positivity
    have hright : 0 ≤ D.curvatureTensorNorm x * H := by
      dsimp only [H]
      positivity
    have hsquare : S ^ 2 ≤ (D.curvatureTensorNorm x * H) ^ 2 := by
      calc
        _ ≤ H ^ 2 * D.curvatureTensorNorm x ^ 2 := hcs
        _ = _ := by ring
    exact (sq_le_sq₀ hS0 hright).mp hsquare
  simp only [hnorm]
  calc
    ‖D.curvature x u v w‖ = ‖R u v w‖ := congrArg norm (hR u v w).symm
    _ = ‖∑ γ : ι × ι × ι, c γ • rb γ‖ := congrArg norm hExpand
    _ ≤ ∑ γ : ι × ι × ι, ‖c γ • rb γ‖ := norm_sum_le _ _
    _ = S := by simp only [S, norm_smul, Real.norm_eq_abs]
    _ ≤ D.curvatureTensorNorm x * H := hbound
    _ = _ := by dsimp only [H]; ring

end PoincareConjecture.RicciFlow.Local
