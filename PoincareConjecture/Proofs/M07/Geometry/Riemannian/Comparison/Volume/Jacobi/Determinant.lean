import PoincareConjecture.Proofs.M07.Analysis.Matrix.Determinant
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Riccati
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology BigOperators

namespace PoincareConjecture.RiemannianMetric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDerivAt_determinantRoot
    {J : ℝ → Matrix ι ι ℝ} {V : Matrix ι ι ℝ} {m t : ℝ}
    (hJ : ∀ i j, HasDerivAt (fun s => J s i j) (V i j) t)
    (hpos : 0 < (J t).det) :
    HasDerivAt (fun s => (J s).det ^ (1 / m))
      ((V * (J t)⁻¹).trace / m * (J t).det ^ (1 / m)) t := by
  have hd := Poincare.Matrix.hasDerivAt_det_eq_det_mul_trace_inv_mul J V t hJ
    hpos.ne'.isUnit
  have heq : ((J t).det * ((J t)⁻¹ * V).trace) * (1 / m) *
      (J t).det ^ (1 / m - 1) =
      (V * (J t)⁻¹).trace / m * (J t).det ^ (1 / m) := by
    rw [Matrix.trace_mul_comm, Real.rpow_sub hpos, Real.rpow_one]
    field_simp
  exact heq ▸ hd.rpow_const (Or.inl hpos.ne')

theorem hasDerivAt_deriv_determinantRoot
    {J V : ℝ → Matrix ι ι ℝ} {m t h' : ℝ}
    (hJ : ∀ᶠ s in 𝓝 t, ∀ i j, HasDerivAt (fun u => J u i j) (V s i j) s)
    (hpos : 0 < (J t).det)
    (hh : HasDerivAt (fun s => (V s * (J s)⁻¹).trace) h' t) :
    HasDerivAt (deriv (fun s => (J s).det ^ (1 / m)))
      ((h' / m + ((V t * (J t)⁻¹).trace / m) ^ 2) * (J t).det ^ (1 / m)) t := by
  have hJt := Filter.Eventually.self_of_nhds hJ
  have hd := hasDerivAt_determinantRoot (m := m) hJt hpos
  have hc := (Poincare.Matrix.differentiableAt_det
    (fun i j => (hJt i j).differentiableAt)).continuousAt
  have hp : ∀ᶠ s in 𝓝 t, 0 < (J s).det := hc (Ioi_mem_nhds hpos)
  have heq : deriv (fun s => (J s).det ^ (1 / m)) =ᶠ[𝓝 t]
      (fun s => (V s * (J s)⁻¹).trace / m * (J s).det ^ (1 / m)) := by
    filter_upwards [hJ, hp] with s hs hsp
    exact (hasDerivAt_determinantRoot hs hsp).deriv
  have he := ((hh.div_const m).mul hd).congr_of_eventuallyEq heq
  convert! he using 1
  ring

theorem deriv2_determinantRoot_le_of_riccati
    {J V : ℝ → Matrix ι ι ℝ} {K : Matrix ι ι ℝ} {κ t : ℝ}
    (hm : 0 < Fintype.card ι)
    (hJ : ∀ᶠ s in 𝓝 t, ∀ i j, HasDerivAt (fun u => J u i j) (V s i j) s)
    (hpos : 0 < (J t).det)
    (hS : (V t * (J t)⁻¹).IsSymm)
    (hS' : ∀ i j, HasDerivAt (fun s => (V s * (J s)⁻¹) i j)
      ((-((V t * (J t)⁻¹) * (V t * (J t)⁻¹)) - K : Matrix ι ι ℝ) i j) t)
    (hRic : -(Fintype.card ι : ℝ) * κ ≤ K.trace) :
    deriv (deriv (fun s => (J s).det ^ (1 / (Fintype.card ι : ℝ)))) t ≤
      κ * (J t).det ^ (1 / (Fintype.card ι : ℝ)) := by
  have hh : HasDerivAt (fun s => (V s * (J s)⁻¹).trace)
      (-((V t * (J t)⁻¹) * (V t * (J t)⁻¹)) - K : Matrix ι ι ℝ).trace t := by
    have heq : (fun s => (V s * (J s)⁻¹).trace) =
        ∑ i, (fun s => (V s * (J s)⁻¹) i i) := by
      funext s
      simp only [Finset.sum_apply, Matrix.trace, Matrix.diag]
    rw [heq]
    exact HasDerivAt.sum (u := Finset.univ) (fun i _ => hS' i i)
  rw [(hasDerivAt_deriv_determinantRoot hJ hpos hh).deriv]
  exact density_root_second_derivative_le (Nat.cast_pos.mpr hm)
    (Real.rpow_pos_of_pos hpos _).le
    (trace_riccati_inequality_of_matrix_equation hm hS rfl hRic) rfl

end PoincareConjecture.RiemannianMetric
