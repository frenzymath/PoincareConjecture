import PoincareConjecture.Proofs.M09.ComparisonLineVariation
import PoincareConjecture.Proofs.M09.ComparisonHessian
import PoincareConjecture.Proofs.M09.AdaptedVariationIndex
import PoincareConjecture.Proofs.M09.LocalHessianTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => Fin n → ℝ

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem comparison_family_laplacian_eq
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (P : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s))
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 (Real.sqrt b) ⊆ U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) U)
    (hP : ∀ i, IsAdaptedFieldOn F T (A.squareFamily Z) (P i) U)
    (hpair : ∀ s ∈ U, ∀ i j, (F.metric (T - s ^ 2)).inner (A.squareFamily Z s)
      (P i s) (P j s) = if i = j then 1 else 0)
    (f : V × ℝ → M) (Ω : Set (V × ℝ)) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn (𝓘(ℝ, V × ℝ)) (𝓡 n) ∞ f Ω)
    (hsegment : ∀ s ∈ Set.Icc 0 (Real.sqrt b), ((0 : V), s) ∈ Ω)
    (hbase : ∀ s, f (0, s) = A.squareFamily Z s)
    (hfixed : ∀ x, f (x, 0) = p)
    (hfields : ∀ s ∈ Set.Icc 0 (Real.sqrt b), ∀ x : V,
      (curveVelocity (n := n) (fun r : ℝ ↦ f (r • x, s)) 0 : E) =
        ∑ i, x i • ((s / Real.sqrt b) • P i s))
    (B : M × ℝ → ℝ) (O : Set M) (hO : IsOpen O) (hqO : A.gamma Z b ∈ O)
    (hB : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun q ↦ B (q, b)) O)
    (hdf : ∀ v : TangentSpace (𝓡 n) (A.gamma Z b),
      mvfderiv (𝓡 n) (fun q ↦ B (q, b)) (A.gamma Z b) v =
        (F.metric (T - b)).inner (A.gamma Z b) (curveVelocity (A.gamma Z) b) v)
    (hpull : (fun z : V × ℝ ↦ B (f (z.1, Real.sqrt z.2), z.2)) =ᶠ[𝓝 (0, b)]
      (fun z ↦ backwardLLength F T 0 z.2 (fun t ↦ f (z.1, Real.sqrt t)) /
        (2 * Real.sqrt z.2))) :
    reducedLengthLaplacian F T B b (A.gamma Z b) =
      (n : ℝ) / (2 * b) - (F.connection (T - b)).scalarCurvature (A.gamma Z b) -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / (2 * b * Real.sqrt b) := by
  classical
  let c := Real.sqrt b
  let K := sqrtParameterInterval 0 b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb.le
  have hcK : c ∈ K := ⟨Real.sqrt_le_sqrt hb.le, le_rfl⟩
  have hKU' : K ⊆ U := by simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hKU
  have hend : A.squareFamily Z c = A.gamma Z b := by
    rw [A.square_agrees Z c ⟨hc.le, Real.sqrt_lt_sqrt hb.le hmax⟩, hc2]
  let Y : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s) :=
    fun i s ↦ (s / c) • P i s
  have hY (i : Fin n) : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨A.squareFamily Z s, Y i s⟩ : TangentBundle (𝓡 n) M)) U :=
    field_smul_smooth (A.squareFamily Z) (P i) (fun s ↦ s / c) U hU hα
      (contDiffOn_id.div_const c) (hP i).smooth
  let HP (i : Fin n) := Classical.choice (nonempty_parametricFieldExtensionOn_compact
    (A.squareFamily Z) (P i) U K hU hKU' isCompact_Icc hα (hP i).smooth)
  let HY (i : Fin n) := Classical.choice (nonempty_parametricFieldExtensionOn_compact
    (A.squareFamily Z) (Y i) U K hU hKU' isCompact_Icc hα (hY i))
  choose W hWbase hWf hWa using fun i : Fin n ↦
    exists_initialFixedLVariation_of_parameter_line hM04 hτmax hwindow A Z b hb hmax
      f Ω hΩ hf hsegment hbase hfixed (Pi.single i (1 : ℝ))
  have hfield (i : Fin n) (s : ℝ) (hs : s ∈ K) :
      (squareVariationField (W i).toLVariation s : E) = (s / c) • P i s := by
    have hline : (fun u ↦ (W i).squareFamily s u) =
        (fun u : ℝ ↦ f (u • Pi.single i (1 : ℝ), s)) := funext (hWf i s)
    change (curveVelocity (fun u ↦ (W i).squareFamily s u) 0 : E) = _
    rw [hline]
    have hs' : s ∈ Set.Icc 0 (Real.sqrt b) := by
      simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hs
    simpa [Pi.single_apply] using hfields s hs' (Pi.single i (1 : ℝ))
  have hpullLine (i : Fin n) : (fun u ↦ B ((W i).squareFamily c u, b)) =ᶠ[𝓝 (0 : ℝ)]
      (fun u ↦ variationLLength (W i).toLVariation u / (2 * c)) := by
    have htend : Tendsto (fun u : ℝ ↦ (u • Pi.single i (1 : ℝ), b)) (𝓝 0) (𝓝 (0, b)) := by
      have hcont : Continuous (fun u : ℝ ↦ (u • Pi.single i (1 : ℝ), b)) :=
        (continuous_id.smul continuous_const).prodMk continuous_const
      simpa only [zero_smul] using hcont.tendsto (0 : ℝ)
    have h := hpull.comp_tendsto htend
    filter_upwards [h] with u hu
    rw [hWf i c u, hWa i u]
    exact hu
  choose D hH using fun i : Fin n ↦ lExponentialFamily_hessian_eq_variation_index
    hM04 hL hτmax hwindow A Z b hb hmax hmin (fun q ↦ B (q, b)) O hO hqO hB
      hdf (W i) (hWbase i) (hpullLine i)
  have hterminal (i : Fin n) : (squareVariationField (W i).toLVariation c : E) = P i c := by
    rw [hfield i c hcK, div_self hc.ne', one_smul]
  have hdiag (i : Fin n) :
      (F.connection (T - b)).hessian (fun q ↦ B (q, b)) (A.gamma Z b) (P i c) (P i c) =
        secondVariationIndexForm (W i).toLVariation (D i) / (2 * c) := by
    have h := hH i
    change (F.connection (T - b)).hessian (fun q ↦ B (q, b)) (A.gamma Z b)
      (squareVariationField (W i).toLVariation c) (squareVariationField (W i).toLVariation c) =
        secondVariationIndexForm (W i).toLVariation (D i) / (2 * c) at h
    rw [hterminal i] at h
    exact h
  have htrace : (∑ i, (F.connection (T - b)).hessian (fun q ↦ B (q, b))
      (A.gamma Z b) (P i c) (P i c)) = reducedLengthLaplacian F T B b (A.gamma Z b) := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - c ^ 2)).toRiemannianMetric⟩
    have hePair (i j : Fin n) : (F.metric (T - c ^ 2)).inner (A.gamma Z b) (P i c) (P j c) =
        if i = j then 1 else 0 := by
      rw [← hend]
      exact hpair c (hKU' hcK) i j
    obtain ⟨e, he⟩ := exists_orthonormalBasis_of_metric_pairing (F.metric (T - c ^ 2))
      (A.gamma Z b) (fun i ↦ (P i c : E)) hePair
    have h := squareTime_laplacian_orthonormal_trace_local F T τmax hτmax hwindow
      (A.gamma Z b) c (htime (hKU' hcK)) (fun q ↦ B (q, b)) O hO hqO hB e
    have h' : (∑ i, (F.connection (T - c ^ 2)).hessian (fun q ↦ B (q, b))
        (A.gamma Z b) (P i c) (P i c)) =
        (F.connection (T - c ^ 2)).laplacian (fun q ↦ B (q, b)) (A.gamma Z b) := by
      simpa only [he] using h
    rw [hc2] at h'
    exact h'
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ ↦ hdiag i)
  rw [htrace, ← Finset.sum_div,
    realized_adapted_variations_index_sum hM04 hτmax hwindow A Z b hb hmax P U hU hKU'
      htime hα hP hpair HP HY W hWbase hfield D] at hsum
  change reducedLengthLaplacian F T B b (A.gamma Z b) =
    ((n : ℝ) / c - 2 * c * (F.connection (T - c ^ 2)).scalarCurvature (A.squareFamily Z c) -
      reducedHarnackIntegral F T (A.gamma Z)
        (backwardScalarEvolutionAlong F T (A.gamma Z)) b / c ^ 2) / (2 * c) at hsum
  rw [hc2, hend] at hsum
  have halgebra (R Q : ℝ) : ((n : ℝ) / c - 2 * c * R - Q / b) / (2 * c) =
      (n : ℝ) / (2 * b) - R - Q / (2 * b * c) := by
    rw [← hc2]
    field_simp [hc.ne'] <;> ring
  exact hsum.trans (halgebra _ _)

end PoincareConjecture.Proofs.M09
