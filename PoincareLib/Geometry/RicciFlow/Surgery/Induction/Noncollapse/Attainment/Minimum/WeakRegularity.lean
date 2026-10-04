import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Minimum.WeakStationarity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.WeakVelocity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.ChartRegularity

/-!
# Continuous derivatives from local weak quadratic minimality

The weak Euler step in Proposition 16.4, p. 369. Positive actual metric
coefficients invert the weak momentum. M08 then gives a continuous
velocity representative and a C1 primitive on the closed interval.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace PoincareMT.M08
export PoincareMT.LGeometry (ChartL2)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (positive_form_operator_isUnit)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (continuousOn_inverse_operator)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (chartForceVector)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (chart_momentum_force_intervalIntegrable)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (weak_momentum_of_chart_stationarity)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (weak_velocity_regular)
end PoincareMT.M08
namespace PoincareMT.M08
export PoincareMT.LGeometry (inverse_operator_apply)
end PoincareMT.M08

namespace PoincareMT.Proofs.M46

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- A continuous primitive minimizing all compact smooth affine
variations is C1 for positive continuous quadratic coefficients with
continuous spatial derivatives. Source: Proposition 16.4, p. 369. -/
theorem weak_quadratic_minimum_contDiffOn {a b : ℝ} (hab : a < b)
    {S : Set E} (hS : IsOpen S)
    (B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ × E → ℝ)
    (DB : ℝ × E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ × E → E →L[ℝ] ℝ)
    (hB : ContinuousOn B (Icc a b ×ˢ S)) (hV : ContinuousOn V (Icc a b ×ˢ S))
    (hDB : ContinuousOn DB (Icc a b ×ˢ S)) (hDV : ContinuousOn DV (Icc a b ×ˢ S))
    (hBd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => B (z.1, x)) (DB z) z.2)
    (hVd : ∀ z ∈ Icc a b ×ˢ S, HasFDerivAt (fun x => V (z.1, x)) (DV z) z.2)
    (hsym : ∀ z ∈ Icc a b ×ˢ S, ∀ v w : E, B z v w = B z w v)
    (hpos : ∀ z ∈ Icc a b ×ˢ S, ∀ v : E, v ≠ 0 → 0 < B z v v)
    (u : ℝ → E) (hu : ContinuousOn u (Icc a b)) (hmem : MapsTo u (Icc a b) S)
    (w : M08.ChartL2 E a b)
    (hprimitive : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, w r)
    (hmin : ∀ eta : ℝ → E, ContDiff ℝ ∞ eta → tsupport eta ⊆ Ioo a b →
      IsLocalMin (fun e : ℝ => ∫ s in a..b,
        B (s, u s + e • eta s) (w s + e • deriv eta s) (w s + e • deriv eta s) / 2 +
          V (s, u s + e • eta s)) 0) :
    ContDiffOn ℝ 1 u (Icc a b) := by
  let graph (s : ℝ) := (s, u s)
  have hgraph : ContinuousOn graph (Icc a b) := continuousOn_id.prodMk hu
  have hgraphmem : MapsTo graph (Icc a b) (Icc a b ×ˢ S) :=
    fun _ hs => ⟨hs, hmem hs⟩
  let G := B ∘ graph
  let DG := DB ∘ graph
  let D := DV ∘ graph
  have hG : ContinuousOn G (Icc a b) := hB.comp hgraph hgraphmem
  have hDG : ContinuousOn DG (Icc a b) := hDB.comp hgraph hgraphmem
  have hD : ContinuousOn D (Icc a b) := hDV.comp hgraph hgraphmem
  obtain ⟨C, hC, hbound⟩ := compact_three_norm_bounds isCompact_Icc G DG D hG hDG hD
  let A (s : ℝ) := InnerProductSpace.continuousLinearMapOfBilin (G s)
  let inverse (s : ℝ) := Ring.inverse (A s)
  have hA : ContinuousOn A (Icc a b) := continuousOn_const.clm_comp hG
  have hunit (s : ℝ) (hs : s ∈ Icc a b) : IsUnit (A s) :=
    M08.positive_form_operator_isUnit _ (hpos (graph s) (hgraphmem hs))
  have hinverse : ContinuousOn inverse (Icc a b) := M08.continuousOn_inverse_operator A hA hunit
  let Q (s : ℝ) := M08.chartForceVector (DG s) (D s) (w s)
  obtain ⟨hP, hQ⟩ := M08.chart_momentum_force_intervalIntegrable hab.le hC w (Lp.memLp w)
    G DG D hG hDG hD hbound
  have hweak : ∀ phi : ℝ → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Ioo a b → (∫ s in a..b, deriv phi s • A s (w s)) =
        -(∫ s in a..b, phi s • Q s) := by
    intro phi hphi _ hsupp
    have hstationary (z : E) :
        (∫ s in a..b, DG s (phi s • z) (w s) (w s) / 2 +
          G s (w s) (deriv phi s • z) + D s (phi s • z)) = 0 := by
      let eta (s : ℝ) := phi s • z
      have heta : ContDiff ℝ ∞ eta := hphi.smul contDiff_const
      have hetasupp : tsupport eta ⊆ Ioo a b :=
        (tsupport_smul_subset_left phi (fun _ : ℝ => z)).trans hsupp
      have hetad : deriv eta = fun s => deriv phi s • z := by
        ext s
        exact deriv_smul_const ((hphi.differentiable (by simp)) s) z
      have h := weak_quadratic_affine_stationary hab.le hS B V DB DV hB hV hDB hDV
        hBd hVd hsym u w hu hmem (Lp.memLp w) eta (deriv eta)
        heta.continuous.continuousOn (heta.continuous_deriv (by simp)).continuousOn
        (hmin eta heta hetasupp)
      simpa only [hetad, eta, G, DG, D, Function.comp_apply, graph] using h
    exact (M08.weak_momentum_of_chart_stationarity hab.le hC w (Lp.memLp w)
      G DG D hG hDG hD hbound phi hphi hstationary).2.2
  obtain ⟨_, _, _, _, _, _, _, _, hreg⟩ := M08.weak_velocity_regular hab u w hprimitive
    A inverse hA hinverse (fun s hs v => M08.inverse_operator_apply _ (hunit s hs) v)
    Q hQ hP hweak
  exact hreg

end PoincareMT.Proofs.M46
