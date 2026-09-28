import PoincareConjecture.Proofs.M09.WithinEquationCongruence
import PoincareConjecture.Proofs.M09.InitialVectorIdentification

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_squareSlice_contMDiffOn (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z)
      ((fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.squareFamily z.1 z.2) A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hi : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E × ℝ)) ∞ (fun s : ℝ ↦ (Z, s)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff
  exact hf.comp hi.contMDiffOn (fun s hs ↦ hs)

theorem lExponentialFamily_localRegularizedEquation_closed
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (s : ℝ) (hs : s ∈ sqrtParameterInterval 0 b) :
    LocalRegularizedEquation F T (A.squareFamily Z) s := by
  let R := A.regularization Z b hb hmax
  let K := sqrtParameterInterval 0 b
  let U := (fun r : ℝ ↦ (Z, r)) ⁻¹' A.squareDomain
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp [K, sqrtParameterInterval]
  have hKd : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc (Real.sqrt_pos.mpr hb)
  have hU : IsOpen U := A.square_open.preimage (continuous_const.prodMk continuous_id)
  have hKU : K ⊆ U := by
    intro r hr
    have hr0 : 0 ≤ r := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hr.1
    exact A.square_contains ⟨Set.mem_univ _, hr0,
      hr.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs0,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have heq := (regularizedEquation_iff_local F hM04 T τmax hτmax hwindow
    R.path.curve R.path.domain K R.path.open_domain R.path.interval_subset hKd
    R.path.smooth R.velocity_extension s hs htime).mp (R.equation s hs)
  exact heq.congr_of_eqOn K R.path.domain U R.path.open_domain hU
    R.path.interval_subset hKU R.path.smooth (lExponentialFamily_squareSlice_contMDiffOn A Z)
    hKd (lExponentialFamily_regularization_eqOn A Z b hb hmax) hs

end PoincareConjecture.Proofs.M09
