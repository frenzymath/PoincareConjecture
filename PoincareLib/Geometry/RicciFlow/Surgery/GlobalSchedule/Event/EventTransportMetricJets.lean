import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Event.EventTransportMetric
import PoincareLib.Analysis.Calculus.SmoothCompactness.Pullback
import PoincareLib.Analysis.Calculus.SmoothCompactness.LocalConvergence
import PoincareLib.Analysis.Calculus.SmoothCompactness.LinearPostcompose
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets

/-!
# Bilinear chart jets of a surgery metric limit

The frozen convergence predicate controls scalar matrix entries. The checked
finite-dimensional component bound upgrades this to the bilinear coefficient
field used by M07's smooth-pullback convergence theorem.
This supplies the regular-limit transport in Morgan--Tian Definition 15.8,
pp. 361-362; the explicit chart argument is recorded in
`proof-work/tasks/M51/derivations/2026-09-24-event-transport.md`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M51EventTransport

local notation "V3" => EuclideanSpace ℝ (Fin 3)
local notation "Bil3" => V3 →L[ℝ] V3 →L[ℝ] ℝ

local instance : NormedAddCommGroup (V3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (V3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Bil3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (Bil3) := ContinuousLinearMap.toNormedSpace

/-- Uniform convergence of the nine scalar entries controls every bilinear jet,
for the regular-limit clause of Definition 15.8, pp. 361-362. -/
theorem bilinear_jets_of_scalar_jets
    {ι : Type*} {l : Filter ι} {K : Set V3}
    {B : ι → V3 → Bil3} {B₀ : V3 → Bil3}
    (hB : ∀ i x, x ∈ K → ContDiffAt ℝ ∞ (B i) x)
    (hB₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ B₀ x)
    (m : ℕ)
    (hscalar : ∀ a b : Fin 3,
      TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ m (fun x => B i x
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)))
        (iteratedFDeriv ℝ m (fun x => B₀ x
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b))) l K) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ m (B i))
      (iteratedFDeriv ℝ m B₀) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  have hentries : ∀ᶠ i in l, ∀ a b : Fin 3, ∀ x ∈ K,
      dist (iteratedFDeriv ℝ m (fun y => B₀ y
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) x)
        (iteratedFDeriv ℝ m (fun y => B i y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) x) < eta / 10 := by
    simp only [Filter.eventually_all]
    intro a b
    exact Metric.tendstoUniformlyOn_iff.mp (hscalar a b) (eta / 10) (by positivity)
  filter_upwards [hentries] with i hi x hx
  have hm : (m : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hbound := SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components
    (EuclideanSpace.basisFun (Fin 3) ℝ) ((hB i x hx).sub (hB₀ x hx)) m
    (C := eta / 10) ?_
  · rw [fun_iteratedFDeriv_sub_apply ((hB i x hx).of_le hm)
      ((hB₀ x hx).of_le hm)] at hbound
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt hbound (by norm_num; linarith)
  · intro a b
    change ‖iteratedFDeriv ℝ m ((fun y => B i y
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) - (fun y => B₀ y
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b))) x‖ ≤ eta / 10
    rw [iteratedFDeriv_sub_apply
      ((((hB i x hx).clm_apply contDiffAt_const).clm_apply contDiffAt_const).of_le hm)
      ((((hB₀ x hx).clm_apply contDiffAt_const).clm_apply contDiffAt_const).of_le hm)]
    simpa only [dist_eq_norm, norm_sub_rev] using (hi a b x hx).le

/-- The source chart restricted to its regular-limit region;
Definition 15.8, pp. 361-362. -/
def chartRegularDomain (A : GeneralizedSliceCarrier.{u})
    (q : A.carrier) (U : Set A.carrier) : Set V3 :=
  (extChartAt (𝓡 3) q).target ∩ (extChartAt (𝓡 3) q).symm ⁻¹' U

/-- Restricting a chart to the open regular-limit region gives an open domain;
Definition 15.8, pp. 361-362. -/
theorem chartRegularDomain_open (A : GeneralizedSliceCarrier.{u})
    (q : A.carrier) {U : Set A.carrier} (hU : IsOpen U) :
    IsOpen (chartRegularDomain A q U) :=
  (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU

/-- The terminal coefficient field is smooth on the regular chart domain;
Definition 15.8, pp. 361-362. -/
theorem terminal_chart_contDiffOn
    {A B : GeneralizedSliceCarrier.{u}} (gT : RiemannianMetric 3 B.carrier)
    {f : A.carrier → B.carrier} {U : Set A.carrier} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (q : A.carrier) :
    ContDiffOn ℝ ∞
      (gT.pullbackCoefficients (f ∘ (extChartAt (𝓡 3) q).symm))
      (chartRegularDomain A q U) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply gT.contDiffAt_pullbackCoefficients
  exact (hf.contMDiffAt (hU.mem_nhds hx.2)).comp x
    ((contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hx.1))

/-- Along a convergent time sequence, all bilinear source-chart jets converge;
Definition 15.8, pp. 361-362. -/
theorem metricLimit_chart_jets_seq
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier}
    {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hlim : SurgeryMetricLimitOn A B g gT f U T)
    (q : A.carrier) (hq : q ∈ U)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[<] T))
    (m : ℕ) (K : Set V3) (hK : IsCompact K)
    (hKU : K ⊆ chartRegularDomain A q U) :
    TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m
        ((g (t i)).pullbackCoefficients (extChartAt (𝓡 3) q).symm))
      (iteratedFDeriv ℝ m
        (gT.pullbackCoefficients (f ∘ (extChartAt (𝓡 3) q).symm))) atTop K := by
  apply bilinear_jets_of_scalar_jets
    (fun i x hx => ((g (t i)).contDiffOn_chartCoefficients q).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hKU hx).1))
    (fun x hx => (terminal_chart_contDiffOn gT hU hf q).contDiffAt
      ((chartRegularDomain_open A q hU).mem_nhds (hKU hx)))
  intro a b
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨d, hd, hbound⟩ := hlim q hq K hK (fun x hx => (hKU hx).1)
    (by rintro _ ⟨x, hx, rfl⟩; exact (hKU hx).2) m a b eta heta
  have htime : Ioo (T - d) T ∈ 𝓝[<] T :=
    (nhdsLT_basis T).mem_of_mem (by linarith)
  filter_upwards [ht htime] with i hi x hx
  change dist (iteratedFDeriv ℝ m
      (surgeryMetricCoefficient gT (fun z => f ((extChartAt (𝓡 3) q).symm z)) a b) x)
    (iteratedFDeriv ℝ m (singularMetricCoefficient (g (t i)) q a b) x) < eta
  simpa only [dist_eq_norm, norm_sub_rev] using hbound (t i) hi.1 hi.2 x hx

end PoincareMT.M51EventTransport
