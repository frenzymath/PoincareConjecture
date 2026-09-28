import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Time

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Poincare.Analysis.Dirichlet.Kernel

section Rows

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace X]

private def evaluationRowCLM (x : X) : (E →L[ℝ] (X →ᵇ ℝ)) →L[ℝ] E :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.compL ℝ E (X →ᵇ ℝ) ℝ (BoundedContinuousFunction.evalCLM ℝ x))

private theorem evaluationRowCLM_apply (x : X) (T : E →L[ℝ] (X →ᵇ ℝ)) :
    evaluationRowCLM x T = evaluationRow T x := rfl

private theorem evaluationRow_dist_le (x : X) (T U : E →L[ℝ] (X →ᵇ ℝ)) :
    dist (evaluationRow T x) (evaluationRow U x) ≤ dist T U := by
  change dist (evaluationRowCLM x T) (evaluationRowCLM x U) ≤ dist T U
  rw [dist_eq_norm, ← map_sub, evaluationRowCLM_apply]
  convert! norm_evaluationRow_le (T - U) x using 1
  exact dist_eq_norm T U

private theorem continuous_evaluationRow_compact :
    Continuous (fun p : {T : E →L[ℝ] (X →ᵇ ℝ) // IsCompactOperator T} × X =>
      evaluationRow p.1.1 p.2) := by
  have ha (T : {T : E →L[ℝ] (X →ᵇ ℝ) // IsCompactOperator T}) :
      Continuous (fun x : X => evaluationRow T.1 x) :=
    continuous_evaluationRow T.1 T.2
  have hb (x : X) : LipschitzWith 1
      (fun T : {T : E →L[ℝ] (X →ᵇ ℝ) // IsCompactOperator T} => evaluationRow T.1 x) := by
    convert! LipschitzWith.mk_one (fun T U :
      {T : E →L[ℝ] (X →ᵇ ℝ) // IsCompactOperator T} =>
        evaluationRow_dist_le x T.1 U.1) using 1
  convert! continuous_prod_of_continuous_lipschitzWith
    (fun p : {T : E →L[ℝ] (X →ᵇ ℝ) // IsCompactOperator T} × X =>
      evaluationRow p.1.1 p.2) 1 ha hb using 1

private theorem continuous_rowGram_family {A : Type*} [TopologicalSpace A]
    (T : A → E →L[ℝ] (X →ᵇ ℝ)) (hT : Continuous T)
    (hc : ∀ a, IsCompactOperator (T a)) :
    Continuous (fun p : (X × X) × A =>
      inner ℝ (evaluationRow (T p.2) p.1.1) (evaluationRow (T p.2) p.1.2)) := by
  have hTc : Continuous (fun a => (⟨T a, hc a⟩ :
      {T : E →L[ℝ] (X →ᵇ ℝ) // IsCompactOperator T})) := hT.subtype_mk _
  have hrow : Continuous (fun p : A × X => evaluationRow (T p.1) p.2) :=
    (continuous_evaluationRow_compact (E := E) (X := X)).comp
      ((hTc.comp continuous_fst).prodMk continuous_snd)
  have hx := hrow.comp (show Continuous (fun p : (X × X) × A => (p.2, p.1.1)) from
    continuous_snd.prodMk continuous_fst.fst)
  have hy := hrow.comp (show Continuous (fun p : (X × X) × A => (p.2, p.1.2)) from
    continuous_snd.prodMk continuous_fst.snd)
  exact hx.inner hy

end Rows

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}
  (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

def heatKernelContinuousTime (t : ℝ) (x y : M) : ℝ :=
  inner ℝ (evaluationRow (Boundary.heatPowerContinuousTime D S 0 (t / 2)) x)
    (evaluationRow (Boundary.heatPowerContinuousTime D S 0 (t / 2)) y)

theorem heatKernelContinuousTime_of_pos {t : ℝ} (ht : 0 < t) (x y : M) :
    heatKernelContinuousTime D S t x y = heatKernelContinuous D S t ht x y := by
  simp only [heatKernelContinuousTime, heatKernelContinuous,
    Boundary.heatPowerContinuousTime_of_pos D S 0 (half_pos ht)]

theorem continuous_heatKernelContinuous_joint :
    Continuous (fun p : (M × M) × Ioi (0 : ℝ) =>
      heatKernelContinuous D S (p.2 : ℝ) p.2.property p.1.1 p.1.2) := by
  let T : Ioi (0 : ℝ) →
      Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] (M →ᵇ ℝ) :=
    fun t => Boundary.heatPowerContinuous D S 0 (t / 2) (half_pos t.2)
  have hT : Continuous T := by
    have h := (Boundary.contDiffOn_heatPowerContinuousTime D S 0).continuousOn.comp_continuous
      (continuous_subtype_val.div_const (2 : ℝ))
      (fun t : Ioi (0 : ℝ) => (show (0 : ℝ) < (t : ℝ) / 2 from half_pos t.2))
    apply h.congr
    intro t
    exact Boundary.heatPowerContinuousTime_of_pos D S 0 (half_pos t.2)
  exact continuous_rowGram_family T hT (fun t =>
    Boundary.isCompactOperator_heatPowerContinuous D S 0 (t / 2) (half_pos t.2))

theorem contDiffOn_heatKernelContinuousTime (x y : M) :
    ContDiffOn ℝ ∞ (fun t : ℝ => heatKernelContinuousTime D S t x y) (Ioi 0) := by
  have hT : ContDiffOn ℝ ∞
      (fun t : ℝ => Boundary.heatPowerContinuousTime D S 0 (t / 2)) (Ioi 0) :=
    (Boundary.contDiffOn_heatPowerContinuousTime D S 0).comp
      (contDiff_id.div_const (2 : ℝ)).contDiffOn (by
        intro t ht
        change 0 < t / 2
        exact half_pos ht)
  have hrow (z : M) : ContDiffOn ℝ ∞
      (fun t : ℝ => evaluationRow (Boundary.heatPowerContinuousTime D S 0 (t / 2)) z)
      (Ioi 0) := by
    exact (evaluationRowCLM (E := Lp ℝ 2 (g.volumeMeasure.restrict Ω)) z).contDiff.comp_contDiffOn hT
  exact (hrow x).inner ℝ (hrow y)

end PoincareConjecture.LeviCivitaData.Dirichlet
