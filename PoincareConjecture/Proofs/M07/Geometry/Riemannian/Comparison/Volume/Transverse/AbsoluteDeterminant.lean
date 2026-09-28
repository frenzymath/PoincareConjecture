import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Compression
import Mathlib.Analysis.Calculus.Deriv.Abs








noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology BigOperators

namespace PoincareConjecture.RiemannianMetric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDerivAt_abs_determinantRoot
    {J : ℝ → Matrix ι ι ℝ} {V : Matrix ι ι ℝ} {m t : ℝ}
    (hJ : ∀ i j, HasDerivAt (fun s => J s i j) (V i j) t)
    (hne : (J t).det ≠ 0) :
    HasDerivAt (fun s => |(J s).det| ^ (1 / m))
      ((V * (J t)⁻¹).trace / m * |(J t).det| ^ (1 / m)) t := by
  have hd := Poincare.Matrix.hasDerivAt_det_eq_det_mul_trace_inv_mul J V t hJ hne.isUnit
  rw [Matrix.trace_mul_comm] at hd
  have ha : HasDerivAt (fun s => |(J s).det|)
      (|(J t).det| * (V * (J t)⁻¹).trace) t := by
    convert! (hasDerivAt_abs hne).comp t hd using 1
    obtain hn | hp := hne.lt_or_gt
    · simp [hn, abs_of_neg hn]
    · simp [hp, abs_of_pos hp]
  have hp : 0 < |(J t).det| := abs_pos.mpr hne
  have heq : (|(J t).det| * (V * (J t)⁻¹).trace) * (1 / m) *
      |(J t).det| ^ (1 / m - 1) =
      (V * (J t)⁻¹).trace / m * |(J t).det| ^ (1 / m) := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    field_simp
  exact heq ▸ ha.rpow_const (Or.inl hp.ne')

theorem hasDerivAt_deriv_abs_determinantRoot
    {J V : ℝ → Matrix ι ι ℝ} {m t h' : ℝ}
    (hJ : ∀ᶠ s in 𝓝 t, ∀ i j, HasDerivAt (fun u => J u i j) (V s i j) s)
    (hne : (J t).det ≠ 0)
    (hh : HasDerivAt (fun s => (V s * (J s)⁻¹).trace) h' t) :
    HasDerivAt (deriv (fun s => |(J s).det| ^ (1 / m)))
      ((h' / m + ((V t * (J t)⁻¹).trace / m) ^ 2) * |(J t).det| ^ (1 / m)) t := by
  have hJt := hJ.self_of_nhds
  have hd := hasDerivAt_abs_determinantRoot (m := m) hJt hne
  have hc := (Poincare.Matrix.differentiableAt_det
    (fun i j => (hJt i j).differentiableAt)).continuousAt
  have hp : ∀ᶠ s in 𝓝 t, (J s).det ≠ 0 := hc.eventually_ne hne
  have heq : deriv (fun s => |(J s).det| ^ (1 / m)) =ᶠ[𝓝 t]
      (fun s => (V s * (J s)⁻¹).trace / m * |(J s).det| ^ (1 / m)) := by
    filter_upwards [hJ, hp] with s hs hsp
    exact (hasDerivAt_abs_determinantRoot hs hsp).deriv
  have he := ((hh.div_const m).mul hd).congr_of_eventuallyEq heq
  convert! he using 1
  ring


theorem deriv2_abs_determinantRoot_le_of_riccati
    {J V : ℝ → Matrix ι ι ℝ} {K : Matrix ι ι ℝ} {κ t : ℝ}
    (hm : 0 < Fintype.card ι)
    (hJ : ∀ᶠ s in 𝓝 t, ∀ i j, HasDerivAt (fun u => J u i j) (V s i j) s)
    (hne : (J t).det ≠ 0)
    (hS : (V t * (J t)⁻¹).IsSymm)
    (hS' : ∀ i j, HasDerivAt (fun s => (V s * (J s)⁻¹) i j)
      ((-((V t * (J t)⁻¹) * (V t * (J t)⁻¹)) - K : Matrix ι ι ℝ) i j) t)
    (hRic : -(Fintype.card ι : ℝ) * κ ≤ K.trace) :
    deriv (deriv (fun s => |(J s).det| ^ (1 / (Fintype.card ι : ℝ)))) t ≤
      κ * |(J t).det| ^ (1 / (Fintype.card ι : ℝ)) := by
  have hh : HasDerivAt (fun s => (V s * (J s)⁻¹).trace)
      (-((V t * (J t)⁻¹) * (V t * (J t)⁻¹)) - K : Matrix ι ι ℝ).trace t := by
    have heq : (fun s => (V s * (J s)⁻¹).trace) =
        ∑ i, (fun s => (V s * (J s)⁻¹) i i) := by
      funext s
      simp only [Finset.sum_apply, Matrix.trace, Matrix.diag]
    rw [heq]
    exact HasDerivAt.sum (u := Finset.univ) (fun i _ => hS' i i)
  rw [(hasDerivAt_deriv_abs_determinantRoot hJ hne hh).deriv]
  exact density_root_second_derivative_le (Nat.cast_pos.mpr hm)
    (Real.rpow_nonneg (abs_nonneg _) _)
    (trace_riccati_inequality_of_matrix_equation hm hS rfl hRic) rfl

theorem deriv2_abs_determinantRoot_le_of_jacobi
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E)
    {J V K : ℝ → E →L[ℝ] E} {a t κ : ℝ}
    (hm : 0 < Fintype.card ι)
    (hJ : ∀ s ∈ Set.Icc 0 a, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 a, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 a, LinearMap.IsSymmetric (K s).toLinearMap)
    (hzero : J 0 = 0) (ht : t ∈ Set.Ioo 0 a)
    (hinv : ∀ᶠ s in 𝓝 t, (J s).IsInvertible)
    (hne : (LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).det ≠ 0)
    (hRic : -(Fintype.card ι : ℝ) * κ ≤
      (LinearMap.toMatrix b.toBasis b.toBasis (K t).toLinearMap).trace) :
    deriv (deriv (fun s =>
      |(LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).det| ^
        (1 / (Fintype.card ι : ℝ)))) t ≤
      κ * |(LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).det| ^
        (1 / (Fintype.card ι : ℝ)) := by
  have ht' : t ∈ Set.Icc 0 a := ⟨ht.1.le, ht.2.le⟩
  have hi := hinv.self_of_nhds
  apply deriv2_abs_determinantRoot_le_of_riccati hm (V := fun s =>
    LinearMap.toMatrix b.toBasis b.toBasis (V s).toLinearMap)
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hasDerivAt_toMatrix_operator b (hJ s ⟨hs.1.le, hs.2.le⟩)
  · exact hne
  · exact isSymm_jacobi_matrix_logarithmicDerivative b hJ hV hK hzero ht' hi
  · exact hasDerivAt_jacobi_matrix_logarithmicDerivative b (hJ t ht') (hV t ht') hinv
  · exact hRic



theorem deriv2_abs_transverse_determinantRoot_le_of_jacobi
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E)
    {J V K : ℝ → E →L[ℝ] E} {a t κ : ℝ}
    (hm : 0 < m)
    (hJ : ∀ s ∈ Set.Icc 0 a, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 a, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 a, LinearMap.IsSymmetric (K s).toLinearMap)
    (hrad : ∀ s ∈ Set.Icc 0 a, K s (b 0) = 0)
    (hzero : J 0 = 0) (ht : t ∈ Set.Ioo 0 a)
    (hne : ((LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).submatrix
      Fin.succ Fin.succ).det ≠ 0)
    (hRic : -(m : ℝ) * κ ≤
      ((LinearMap.toMatrix b.toBasis b.toBasis (K t).toLinearMap).submatrix
        Fin.succ Fin.succ).trace) :
    deriv (deriv (fun s =>
      |((LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det| ^ (1 / (m : ℝ)))) t ≤
      κ * |((LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).submatrix
        Fin.succ Fin.succ).det| ^ (1 / (m : ℝ)) := by
  let c := EuclideanSpace.basisFun (Fin m) ℝ
  have ht' : t ∈ Set.Icc 0 a := ⟨ht.1.le, ht.2.le⟩
  have hJT (s : ℝ) (hs : s ∈ Set.Icc 0 a) := hasDerivAt_transverseOperator b (hJ s hs)
  have hVT (s : ℝ) (hs : s ∈ Set.Icc 0 a) :
      HasDerivAt (fun r => transverseOperator b (V r))
        (-((transverseOperator b (K s)).comp (transverseOperator b (J s)))) s := by
    simpa only [transverseOperator_neg, transverseOperator_comp b _ _ (hrad s hs)] using
      hasDerivAt_transverseOperator b (hV s hs)
  have hd : ContinuousAt (fun s =>
      ((LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det) t :=
    (Poincare.Matrix.differentiableAt_det (G := fun s =>
      (LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).submatrix Fin.succ Fin.succ)
      (fun i j => (hasDerivAt_toMatrix_operator b (hJ t ht') i.succ j.succ).differentiableAt)).continuousAt
  have hi : ∀ᶠ s in 𝓝 t, (transverseOperator b (J s)).IsInvertible := by
    filter_upwards [hd.eventually_ne hne] with s hs
    apply isInvertible_of_toMatrix_det_ne_zero c.toBasis
    simpa only [c, toMatrix_transverseOperator] using hs
  simpa only [c, toMatrix_transverseOperator, Fintype.card_fin] using
    deriv2_abs_determinantRoot_le_of_jacobi c
      (J := fun s => transverseOperator b (J s))
      (V := fun s => transverseOperator b (V s))
      (K := fun s => transverseOperator b (K s))
      (a := a) (t := t) (κ := κ) (by simpa using hm) hJT hVT
      (fun s hs => isSymmetric_transverseOperator b (K s) (hK s hs))
      (by simp [hzero]) ht hi (by simpa only [c, toMatrix_transverseOperator] using hne)
      (by simpa only [c, toMatrix_transverseOperator, Fintype.card_fin] using hRic)

end PoincareConjecture.RiemannianMetric
