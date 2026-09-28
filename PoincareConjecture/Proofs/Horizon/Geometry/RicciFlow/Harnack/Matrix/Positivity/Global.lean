import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.DirectionContact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.ReferenceFrame
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.FrameChange
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Localization
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.FirstContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture Poincare.VectorBundle

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {J : Set ℝ}

private def normalizedDirections (g : RiemannianMetric n M) (V : Set M) :
    Set (HamiltonDirection n M) :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  {q | q.1.val.1 ∈ V ∧ Orthonormal ℝ (FiberFamily.vector q.1) ∧ ‖q.2‖ = 1 ∧
    ∀ i j, q.2 (Sum.inl (i, j)) = -q.2 (Sum.inl (j, i))}

private lemma isCompact_normalizedDirections_over (g : RiemannianMetric n M)
    (V : Set M) {K : Set M} (hK : IsCompact K) (hKV : K ⊆ V) :
    IsCompact {q : normalizedDirections g V | q.val.1.val.1 ∈ K} := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert isCompact_normalized_hamilton_directions g hK using 1
  ext q
  simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right,
    exists_eq_right, normalizedDirections]
  constructor
  · tauto
  · intro h
    exact ⟨⟨hKV h.1, h.2⟩, h.1⟩

private def frameDirection (x : M) (e : Fin n → TangentSpace (𝓡 n) x)
    (z : EuclideanSpace ℝ ((Fin n × Fin n) ⊕ Fin n)) : HamiltonDirection n M :=
  (⟨(x, fun i => ⟨x, e i⟩), fun _ => rfl⟩, z)

omit [T2Space M] in
private lemma perturbed_block_of_normalized_nonneg
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (g : RiemannianMetric n M) (V : Set M) (T₀ : ℝ) {t : ℝ} (ht : t ∈ interior J)
    (φ : ℝ × M → ℝ) (ψ : ℝ → ℝ)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ (t, x)))
    (hpos : ∀ q : normalizedDirections g V,
      0 ≤ perturbedHamiltonDirectionQuadratic F T₀ φ ψ t q) (x : M) (hx : x ∈ V) :
    let b := (F.metric t).orthonormalBasis x
    (Matrix.fromBlocks
      (fun ac de : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
          Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
        (F.connection t).curvatureTensor x (b ac.1) (b ac.2) (b de.1) (b de.2) +
          ψ t * twoFormIdentity ac.1 ac.2 de.1 de.2)
      (fun ac d => hamiltonP (F.connection t) x (b ac.1) (b ac.2) (b d))
      (fun c de => hamiltonP (F.connection t) x (b de.1) (b de.2) (b c))
      (fun a c => hamiltonM (F.connection t) (t - T₀) x (b a) (b c) +
        φ (t, x) * (if a = c then 1 else 0))).PosSemidef := by
  apply perturbedHamiltonBlock_posSemidef_of_reference_unit_tests hC F g ht
    (t - T₀) x (fun x => φ (t, x)) hφ (ψ t)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro e he z hz hskew
  have hn : frameDirection x e z ∈ normalizedDirections g V := ⟨hx, he, hz, hskew⟩
  have h := hpos ⟨frameDirection x e z, hn⟩
  dsimp only [perturbedHamiltonDirectionQuadratic, hamiltonDirectionQuadratic,
    frameDirection, FiberFamily.vector] at h
  simp only [cast_eq] at h
  dsimp only
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at h ⊢
  linarith only [h]

omit [T2Space M] in
private lemma normalized_direction_coordinates
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (g : RiemannianMetric n M) (V : Set M) (T₀ t : ℝ) (φ : ℝ × M → ℝ) (ψ : ℝ → ℝ)
    (q : normalizedDirections g V) :
    ∃ (U : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q.val.1.val.1)) →
        Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q.val.1.val.1)) → ℝ)
      (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q.val.1.val.1)) → ℝ),
      (∀ a b, U a b = -U b a) ∧
      (Real.sqrt (∑ a, ∑ b, (U a b) ^ 2) ≠ 0 ∨ Real.sqrt (∑ a, (W a) ^ 2) ≠ 0) ∧
      ∀ s, perturbedHamiltonDirectionQuadratic F T₀ φ ψ s q =
        perturbedHamiltonFixedQuadratic F T₀ t q.val.1.val.1
          (fun r y => φ (r, y)) ψ U W s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let C := hamiltonFrameCoordinates (F.metric t) q.val.1.val.1 (FiberFamily.vector q.val.1)
  refine ⟨hamiltonTwoFormCoordinates C (fun i j => q.val.2 (Sum.inl (i, j))),
    hamiltonVectorCoordinates C (fun i => q.val.2 (Sum.inr i)),
    hamiltonTwoFormCoordinates_skew C _ q.property.2.2.2, ?_, ?_⟩
  · exact hamiltonDirectionCoordinates_sqrt_nonzero (F.metric t) q.val
      q.property.2.1.linearIndependent q.property.2.2.1
  · exact perturbedHamiltonDirectionQuadratic_eq_fixed hC F T₀ t φ ψ q.val

private theorem normalized_exp_quadratic_pos
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (g : RiemannianMetric n M) {O : M} (S : RicciFlow.SmoothExhaustion F O)
    (V : Set M) (hV : IsOpen V)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r ∧ x ∈ V})
    {T K ε δ A : ℝ} (hT : 0 < T) (hJ : Ioc 0 T ⊆ interior J) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioc 0 T, ∀ x ∈ V, ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (hcurv : ∀ t ∈ Ioc 0 T, ∀ x ∈ V, (F.connection t).NonnegativeCurvatureOperator x)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hA : hamiltonPerturbationErrorBound n K T + (n : ℝ) * S.bound < A)
    (hsmall : hamiltonPerturbationErrorBound n K T * δ ≤ ε)
    (hψone : δ * Real.exp (A * T) ≤ 1) :
    ∀ t ∈ Ioc 0 T, ∀ q : normalizedDirections g V,
      0 < perturbedHamiltonDirectionQuadratic F 0
        (fun p => ε * Real.exp (A * p.1) * S.toFun p.2 / p.1)
        (fun s => δ * Real.exp (A * s)) t q := by
  let φ := fun p : ℝ × M => ε * Real.exp (A * p.1) * S.toFun p.2 / p.1
  let ψ := fun s => δ * Real.exp (A * s)
  let Q := fun (q : normalizedDirections g V) s =>
    perturbedHamiltonDirectionQuadratic F 0 φ ψ s q
  have hApos : 0 < A := by
    have hc := hamiltonPerturbationErrorBound_pos (n := n) hK hT.le
    have hl := mul_nonneg (Nat.cast_nonneg n) S.bound_nonneg
    linarith only [hc, hl, hA]
  let C := 6 * (n : ℝ) ^ 4 * K + 3 * (n : ℝ) ^ 5 * K ^ 2
  have hCnonneg : 0 ≤ C := by dsimp only [C]; positivity
  have hpositive (t : ℝ) (ht : t ∈ Ioc 0 T) (q : normalizedDirections g V)
      (hscalar : ∀ z u w : ℝ, -C * w ^ 2 - C * u * w ≤ z → u ≠ 0 ∨ w ≠ 0 →
        0 < z + φ (t, q.val.1.val.1) * w ^ 2 + ψ t * u ^ 2) : 0 < Q q t := by
    obtain ⟨U, W, hU, hn, heq⟩ := normalized_direction_coordinates hC F g V 0 t φ ψ q
    have hlower := hamilton_quadratic_lower_bound_of_bound (F.connection t)
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) ht.1.le q.val.1.val.1
      (hcurv t ht q.val.1.val.1 q.property.1)
      (hbound t ht q.val.1.val.1 q.property.1) U W hU
    have hp := hscalar _ _ _ hlower hn
    change 0 < perturbedHamiltonDirectionQuadratic F 0 φ ψ t q
    rw [heq t, perturbedHamiltonFixedQuadratic_self F 0 t q.val.1.val.1
      (fun s y => φ (s, y)) ψ U W hU]
    simpa only [sub_zero,
      Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg (W a))),
      Real.sq_sqrt (Finset.sum_nonneg (fun a _ =>
        Finset.sum_nonneg (fun b _ => sq_nonneg (U a b))))] using hp
  obtain ⟨L, hL, hLV, houtside⟩ := S.exists_compact_quadratic_perturbation_pos_on
    V hproper hCnonneg hε hδ hApos.le (T := T)
  obtain ⟨t₀, ht₀, hinitial⟩ := S.exists_initial_time_quadratic_perturbation_pos
    hCnonneg hε hδ hApos.le
  intro t ht q
  let a := min t t₀ / 2
  have ha : 0 < a := half_pos (lt_min ht.1 ht₀)
  have hat : a ≤ t := (half_le_self (le_of_lt (lt_min ht.1 ht₀))).trans (min_le_left _ _)
  have hat₀ : a ≤ t₀ := (half_le_self (le_of_lt (lt_min ht.1 ht₀))).trans (min_le_right _ _)
  have haT : a ≤ T := hat.trans ht.2
  have htime {s : ℝ} (hs : s ∈ Icc a T) : s ∈ Ioc 0 T := ⟨ha.trans_le hs.1, hs.2⟩
  have hφspace (s : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ (s, x)) := by
    simpa only [φ, mul_div_right_comm, Pi.mul_apply] using!
      (contMDiff_const.mul S.smooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => (ε * Real.exp (A * s) / s) * S.toFun y))
  have hcontinuous : ContinuousOn (Function.uncurry Q) (univ ×ˢ Icc a T) := by
    rintro ⟨p, s⟩ hs
    have hspos := (htime hs.2).1
    have hφcont : ContinuousAt φ (s, p.val.1.val.1) := by
      apply ContinuousAt.div _ continuousAt_fst hspos.ne'
      exact ((continuousAt_const.mul ((Real.continuous_exp.continuousAt).comp
        (continuousAt_const.mul continuousAt_fst))).mul
          (S.smooth.continuous.continuousAt.comp continuousAt_snd))
    have hψcont : ContinuousAt ψ s := by dsimp only [ψ]; fun_prop
    exact ((continuousAt_perturbedHamiltonDirectionQuadratic hC F 0 (hJ (htime hs.2))
      (by simpa using hspos.ne') p.val hφcont hψcont).comp
        (f := fun z : normalizedDirections g V × ℝ => (z.2, z.1.val))
        (continuousAt_snd.prodMk (continuousAt_subtype_val.comp continuousAt_fst))).continuousWithinAt
  have hderiv (p : normalizedDirections g V) (s : ℝ) (hs : s ∈ Ioc a T) :
      HasDerivWithinAt (Q p) (deriv (Q p) s) (Icc a T) s := by
    have hs' := htime (Ioc_subset_Icc_self hs)
    apply HasDerivAt.hasDerivWithinAt
    apply DifferentiableAt.hasDerivAt
    apply differentiableAt_perturbedHamiltonDirectionQuadratic hC F 0
      (hJ hs') (by simpa using hs'.1.ne') p.val
    · exact ((S.hasDerivAt_exp_mul ε A s p.val.1.val.1).div
        (hasDerivAt_id s) hs'.1.ne').differentiableAt
    · exact (((hasDerivAt_id s).const_mul A).exp.const_mul δ).differentiableAt
  have hcontact (p : normalizedDirections g V) (s : ℝ) (hs : s ∈ Ioc a T)
      (hzero : Q p s = 0) (hnonneg : ∀ r, 0 ≤ Q r s) : 0 < deriv (Q p) s := by
    have hs' := htime (Ioc_subset_Icc_self hs)
    obtain ⟨U, W, hU, hn, heq⟩ := normalized_direction_coordinates hC F g V 0 s φ ψ p
    have heqfun : Q p = perturbedHamiltonFixedQuadratic F 0 s p.val.1.val.1
        (fun r y => φ (r, y)) ψ U W := funext heq
    have hblock := perturbed_block_of_normalized_nonneg hC F g V 0 (hJ hs')
      φ ψ (hφspace s) hnonneg
    have hψ : δ * Real.exp (A * s) ≤ 1 := le_trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hs'.2 hApos.le)) hδ.le) hψone
    rw [heqfun]
    apply deriv_perturbedHamiltonFixedQuadratic_pos hC S (hJ hs') hs'.1 hs'.2 hK
      p.val.1.val.1 (hbound s hs' p.val.1.val.1 p.property.1) hε hδ hA hsmall hψ U W hU hn
    · filter_upwards [hV.mem_nhds p.property.1] with y hy
      simpa only [sub_zero] using hblock y hy
    · exact (heq s).symm.trans hzero
  have hp := Poincare.Parabolic.pos_of_deriv_pos_at_first_zero_of_pos_outside_compact
    (isCompact_normalizedDirections_over g V hL hLV) hcontinuous hderiv hcontact
    (fun p => hpositive a ⟨ha, haT⟩ p (hinitial a ⟨ha, hat₀⟩ p.val.1.val.1))
    (fun p hp s hs => hpositive s (htime hs) p
      (houtside s (htime hs) p.val.1.val.1 p.property.1 hp))
  exact hp q t ⟨hat, ht.2⟩

theorem hamiltonBlockPos_on_open_set_of_smoothExhaustion
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u})
    {a b T : ℝ} (F : RicciFlow n M (Ioo a b)) (O : M)
    (S : RicciFlow.SmoothExhaustion F O) (V : Set M) (hV : IsOpen V)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r ∧ x ∈ V})
    (hT : 0 < T) (hJ : Ioc 0 T ⊆ Ioo a b)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioc 0 T, ∀ x ∈ V, ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (hcurv : ∀ t ∈ Ioc 0 T, ∀ x ∈ V,
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioc 0 T, ∀ x ∈ V, HamiltonBlockPos F t x t := by
  let C := hamiltonPerturbationErrorBound n K T
  let A := C + (n : ℝ) * S.bound + 1
  let η := (C + 1) / Real.exp (A * T)
  have hCpos : 0 < C := hamiltonPerturbationErrorBound_pos hK hT.le
  have hden : 0 < C + 1 := by linarith
  have hη : 0 < η := div_pos hden (Real.exp_pos _)
  have hrate : C + (n : ℝ) * S.bound < A := by dsimp only [A]; linarith
  have hJ' : Ioc 0 T ⊆ interior (Ioo a b) := by simpa only [interior_Ioo] using hJ
  intro t ht x hx
  have hnonneg (g : RiemannianMetric n M) (q : normalizedDirections g V) :
      0 ≤ hamiltonDirectionQuadratic F 0 t q := by
    let Q := fun ε : ℝ => perturbedHamiltonDirectionQuadratic F 0
      (fun p => ε * Real.exp (A * p.1) * S.toFun p.2 / p.1)
      (fun s => (ε / (C + 1)) * Real.exp (A * s)) t q
    have hcont : Continuous Q := by
      dsimp only [Q, perturbedHamiltonDirectionQuadratic]
      fun_prop
    have hlim : Filter.Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 (hamiltonDirectionQuadratic F 0 t q)) := by
      simpa only [Q, perturbedHamiltonDirectionQuadratic, zero_mul, zero_div, add_zero] using!
        (hcont.continuousAt (x := 0)).tendsto.mono_left
          (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    have hδ : 0 < ε / (C + 1) := div_pos hε.1 hden
    have hsmall : C * (ε / (C + 1)) ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      nlinarith only [hε.1]
    have hψ : (ε / (C + 1)) * Real.exp (A * T) ≤ 1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      have hh := (le_div_iff₀ (Real.exp_pos (A * T))).mp hε.2.le
      simpa only [one_mul] using hh
    exact (normalized_exp_quadratic_pos hC F g S V hV hproper hT hJ' hK hbound hcurv
      hε.1 hδ hrate hsmall hψ t ht q).le
  apply hamiltonBlockPos_of_reference_unit_tests hC F (F.metric t) (hJ ht) t x
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  intro e he z hz hskew
  have hn : frameDirection x e z ∈ normalizedDirections (F.metric t) V := ⟨hx, he, hz, hskew⟩
  have h := hnonneg (F.metric t) ⟨frameDirection x e z, hn⟩
  simpa only [hamiltonDirectionQuadratic, frameDirection, FiberFamily.vector,
    cast_eq, sub_zero] using h

theorem hamiltonBlockPos_of_smoothExhaustion
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u})
    {a b T : ℝ} (F : RicciFlow n M (Ioo a b)) (O : M)
    (S : RicciFlow.SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    (hT : 0 < T) (hJ : Ioc 0 T ⊆ Ioo a b)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioc 0 T, ∀ x, ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (hcurv : ∀ t ∈ Ioc 0 T, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioc 0 T, ∀ x, HamiltonBlockPos F t x t := by
  have hp := hamiltonBlockPos_on_open_set_of_smoothExhaustion hC F O S univ isOpen_univ
    (fun r => by simpa only [mem_univ, and_true] using hproper r) hT hJ hK
    (fun t ht x _ => hbound t ht x) (fun t ht x _ => hcurv t ht x)
  exact fun t ht x => hp t ht x (mem_univ x)

end Poincare.RicciFlow.Harnack
