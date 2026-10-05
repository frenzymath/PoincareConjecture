import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Scalar derivatives along generalized cylinders

Morgan--Tian Lemma 11.2, pp. 268--269, uses scalar time derivatives along
vertical paths. The box metric identity identifies the actual scalar
curvature, and cylinder compatibility identifies each path locally with a
fixed vertical box line. The rescaled clock divides its derivative by the
cylinder scale. Above the scalar guard we retain the derivative witness from
the common controls; elsewhere M04 supplies an unconditional witness.

The derivation and the singleton-time-set check are recorded in
`proof-work/tasks/M30/derivations/scalar-along-cylinder.md`.
-/

set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- A generalized flow box preserves the actual scalar curvature, by its
metric pullback identity (Lemma 11.2, pp. 268--269). -/
theorem scalar_eq_box (F : GeneralizedRicciFlowData.{u}) (b : F.box_index)
    (t : ℝ) (ht : t ∈ (F.box b).interval) (y : (F.box b).carrier.carrier) :
    F.scalar ⟨t, (F.box b).forward t ht y⟩ =
      ((F.box b).flow.connection t).scalarCurvature y := by
  exact (((F.box b).flow.connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ ((F.box b).forward_smooth t ht).contMDiffOn
    (fun z _ v w => ((F.box b).metric_pullback t ht z v w).symm) (mem_univ y)).symm

namespace Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}

/-- The unscaled scalar along a compatible cylinder, totalized by zero
outside its time set (the vertical path in Lemma 11.2, p. 269). -/
noncomputable def scalarAlong (e : GeneralizedFlowCylinder F C origin scale I U)
    (x : C.carrier) (s : ℝ) : ℝ := by
  classical
  exact if hs : s ∈ I then F.scalar (e.pointMap s hs x) else 0

/-- Within the cylinder time set, the scalar function is the actual scalar
at the image spacetime point (Lemma 11.2, p. 269). -/
@[simp] theorem scalarAlong_of_mem (e : GeneralizedFlowCylinder F C origin scale I U)
    (x : C.carrier) {s : ℝ} (hs : s ∈ I) :
    scalarAlong e x s = F.scalar (e.pointMap s hs x) := by
  classical
  exact dif_pos hs

/-- A selected cylinder worldline has the scalar of one fixed box line on
a relative time neighborhood (Lemma 11.2, p. 269). -/
theorem exists_local_scalarAlong_eq_box
    (e : GeneralizedFlowCylinder F C origin scale I U)
    {s : ℝ} (hs : s ∈ I) (x : C.carrier) (hx : x ∈ U) :
    ∃ b : F.box_index, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s' ∈ I, |s' - s| < δ →
        origin + s' / scale ∈ (F.box b).interval ∧
          scalarAlong e x s' =
            ((F.box b).flow.connection (origin + s' / scale)).scalarCurvature y := by
  obtain ⟨b, y, δ, hδ, hlocal⟩ := e.vertical_compatibility s hs x hx
  refine ⟨b, y, δ, hδ, ?_⟩
  intro s' hs' hnear
  obtain ⟨hb, hforward⟩ := hlocal s' hs' hnear
  refine ⟨hb, ?_⟩
  rw [scalarAlong_of_mem e x hs']
  change (F.connection (origin + s' / scale)).scalarCurvature (e.forward s' hs' x) = _
  rw [hforward]
  exact scalar_eq_box F b (origin + s' / scale) hb y

/-- A local box derivative transfers through the affine clock without any
uniqueness assumption on the time set (Lemma 11.2, p. 269). -/
theorem hasDerivWithinAt_scalarAlong_of_local_box
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (x : C.carrier) {s : ℝ} (hs : s ∈ I)
    (b : F.box_index) (y : (F.box b).carrier.carrier)
    {δ : ℝ} (hδ : 0 < δ)
    (hlocal : ∀ s' ∈ I, |s' - s| < δ →
      origin + s' / scale ∈ (F.box b).interval ∧
        scalarAlong e x s' =
          ((F.box b).flow.connection (origin + s' / scale)).scalarCurvature y)
    {d : ℝ}
    (hd : HasDerivWithinAt (fun t => ((F.box b).flow.connection t).scalarCurvature y)
      d (F.box b).interval (origin + s / scale)) :
    HasDerivWithinAt (scalarAlong e x) (d / scale) I s := by
  let V := I ∩ Metric.ball s δ
  have hsV : s ∈ V := ⟨hs, Metric.mem_ball_self hδ⟩
  have hnear (s' : ℝ) (hs' : s' ∈ V) : |s' - s| < δ := by
    simpa only [Real.dist_eq] using Metric.mem_ball.mp hs'.2
  have hclock : HasDerivWithinAt (fun t : ℝ => origin + t / scale) (1 / scale) V s :=
    (((hasDerivAt_id s).div_const scale).const_add origin).hasDerivWithinAt
  have hmap : MapsTo (fun t : ℝ => origin + t / scale) V (F.box b).interval :=
    fun s' hs' => (hlocal s' hs'.1 (hnear s' hs')).1
  have hcomp : HasDerivWithinAt
      (fun t => ((F.box b).flow.connection (origin + t / scale)).scalarCurvature y)
      (d / scale) V s := by
    simpa only [Function.comp_def, mul_one_div] using hd.comp s hclock hmap
  have hscalar := hcomp.congr_of_mem
    (fun s' hs' => (hlocal s' hs'.1 (hnear s' hs')).2) hsV
  exact hscalar.mono_of_mem_nhdsWithin (inter_mem_nhdsWithin I (Metric.ball_mem_nhds s hδ))

/-- M04 supplies an actual within-derivative at every cylinder time, including
points below the scalar guard (Lemma 11.2, p. 269). -/
theorem exists_hasDerivWithinAt_scalarAlong (hC : RicciFlowCurvatureTheory.{u})
    (e : GeneralizedFlowCylinder F C origin scale I U)
    {s : ℝ} (hs : s ∈ I) (x : C.carrier) (hx : x ∈ U) :
    ∃ d : ℝ, HasDerivWithinAt (scalarAlong e x) d I s := by
  obtain ⟨b, y, δ, hδ, hlocal⟩ := exists_local_scalarAlong_eq_box e hs x hx
  have hb := (hlocal s hs (by simpa only [sub_self, abs_zero] using hδ)).1
  exact ⟨_, hasDerivWithinAt_scalarAlong_of_local_box e x hs b y hδ hlocal
    (hC.scalar_evolution 3 (F.box b).carrier.carrier (F.box b).interval
      (F.box b).flow (origin + s / scale) hb y)⟩

/-- Common controls give a guarded derivative bound for the actual scalar
along each backward cylinder line. The witness is chosen from the controls
above the guard, avoiding derivative uniqueness on isolated times
(Lemma 11.2, pp. 268--269). -/
theorem exists_scalarAlong_deriv_bound
    {S : GeneralizedBlowupSequence.{u}} (hC : RicciFlowCurvatureTheory.{u})
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    {k : ℕ}
    (e : GeneralizedFlowCylinder (S.flow k) C (S.base k).1 scale I U)
    {s : ℝ} (hs : s ∈ I) (hs₀ : s ≤ 0) (x : C.carrier) (hx : x ∈ U) :
    ∃ d : ℝ, HasDerivWithinAt (scalarAlong e x) d I s ∧
      (4 * S.scale k ≤ scalarAlong e x s →
        |d| ≤ H.analytic_constant / scale * scalarAlong e x s ^ 2) := by
  by_cases hguard : 4 * S.scale k ≤ scalarAlong e x s
  · obtain ⟨b, y, δ, hδ, hlocal⟩ := exists_local_scalarAlong_eq_box e hs x hx
    obtain ⟨hb, hscalar⟩ := hlocal s hs (by simpa only [sub_self, abs_zero] using hδ)
    have htime : (S.base k).1 + s / scale ≤ (S.base k).1 :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs₀ e.scale_pos.le)
    obtain ⟨d, hd, hbound⟩ := H.scalar_time_derivative_bound k b _ hb htime y
      (hguard.trans_eq hscalar)
    refine ⟨d / scale,
      hasDerivWithinAt_scalarAlong_of_local_box e x hs b y hδ hlocal hd, ?_⟩
    intro _
    rw [abs_div, abs_of_pos e.scale_pos]
    calc
      |d| / scale ≤ (H.analytic_constant *
          (((S.flow k).box b).flow.connection ((S.base k).1 + s / scale)).scalarCurvature y
            ^ 2) / scale := div_le_div_of_nonneg_right hbound e.scale_pos.le
      _ = H.analytic_constant / scale * scalarAlong e x s ^ 2 := by
        rw [hscalar]
        ring
  · obtain ⟨d, hd⟩ := exists_hasDerivWithinAt_scalarAlong hC e hs x hx
    exact ⟨d, hd, fun hg => (hguard hg).elim⟩

end Cylinder

end PoincareMT.M30
