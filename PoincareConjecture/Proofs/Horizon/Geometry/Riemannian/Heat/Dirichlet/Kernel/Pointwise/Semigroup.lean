import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}
  (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

set_option maxHeartbeats 800000 in

theorem heatKernelContinuous_add_eq_inner (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x y : M) :
    heatKernelContinuous D S (s + t) (add_pos hs ht) x y =
      inner ℝ (evaluationRow (heatPowerContinuous D S 0 s hs) x)
        (evaluationRow (heatPowerContinuous D S 0 t ht) y) := by
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have hfac : evaluationRow (heatPowerContinuous D S 0 (s + t) (add_pos hs ht)) x =
      heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure
        t.toNNReal (evaluationRow (heatPowerContinuous D S 0 s hs) x) := by
    apply ext_inner_right ℝ
    intro f
    rw [inner_evaluationRow, heatPowerContinuous_add_comp D S 0 s t hs ht]
    rw [(heatSemigroup_isSelfAdjoint D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure t.toNNReal).isSymmetric.apply_clm]
    exact (inner_evaluationRow (heatPowerContinuous D S 0 s hs) x _).symm
  have hTae := heatPowerContinuous_ae D S 0 t ht
    (evaluationRow (heatPowerContinuous D S 0 s hs) x)
  rw [heatSpectralPower_zero_eq_heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure ht, ← hfac] at hTae
  have hae := (heatKernelContinuous_row_ae D S (s + t) (add_pos hs ht) x).trans hTae.symm
  have hcont : Continuous (heatKernelContinuous D S (s + t) (add_pos hs ht) x) :=
    (continuous_heatKernelContinuous D S (s + t) (add_pos hs ht)).comp
      (continuous_const.prodMk continuous_id)
  have heq : heatKernelContinuous D S (s + t) (add_pos hs ht) x y =
      heatPowerContinuous D S 0 t ht
        (evaluationRow (heatPowerContinuous D S 0 s hs) x) y := by
    by_cases hy : y ∈ Ω
    · exact Measure.eqOn_open_of_ae_eq hae S.isOpen hcont.continuousOn
        (BoundedContinuousFunction.continuous _).continuousOn hy
    · rw [heatKernelContinuous_zero D S _ _ x y (Or.inr hy),
        heatPowerContinuous_zero_outside D S 0 t ht _ y hy]
  exact heq.trans ((inner_evaluationRow (heatPowerContinuous D S 0 t ht) y
    (evaluationRow (heatPowerContinuous D S 0 s hs) x)).symm.trans (real_inner_comm _ _))


theorem heatKernelContinuous_add_eq_heatPowerContinuous
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : M) :
    heatKernelContinuous D S (s + t) (add_pos hs ht) x y =
      heatPowerContinuous D S 0 s hs
        (evaluationRow (heatPowerContinuous D S 0 t ht) y) x :=
  (heatKernelContinuous_add_eq_inner D S s t hs ht x y).trans (inner_evaluationRow _ _ _)


theorem heatKernelContinuous_semigroup (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : M) :
    Integrable (fun z => heatKernelContinuous D S s hs x z * heatKernelContinuous D S t ht z y)
      (g.volumeMeasure.restrict Ω) ∧
    heatKernelContinuous D S (s + t) (add_pos hs ht) x y =
      ∫ z, heatKernelContinuous D S s hs x z * heatKernelContinuous D S t ht z y
        ∂(g.volumeMeasure.restrict Ω) := by
  let u := evaluationRow (heatPowerContinuous D S 0 s hs) x
  let v := evaluationRow (heatPowerContinuous D S 0 t ht) y
  have hae : (fun z => heatKernelContinuous D S s hs x z *
      heatKernelContinuous D S t ht z y) =ᵐ[g.volumeMeasure.restrict Ω]
        fun z => inner ℝ (u z) (v z) := by
    filter_upwards [heatKernelContinuous_row_ae D S s hs x,
      heatKernelContinuous_row_ae D S t ht y] with z hz hz'
    rw [heatKernelContinuous_symm D S t ht z y, hz, hz']
    simp [u, v, mul_comm]
  refine ⟨(L2.integrable_inner (𝕜 := ℝ) u v).congr hae.symm, ?_⟩
  rw [heatKernelContinuous_add_eq_inner D S s t hs ht x y, L2.inner_def]
  exact (integral_congr_ae hae).symm

end PoincareConjecture.LeviCivitaData.Dirichlet
