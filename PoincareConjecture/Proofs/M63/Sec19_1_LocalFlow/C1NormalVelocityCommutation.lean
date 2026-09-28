import PoincareConjecture.Proofs.M63.Mathlib.C1MixedDerivative
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1ChartPullback
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem pullback_velocity_commute_of_time_velocity_c1
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (c : ℝ → ℝ → M)
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1
      (fun z : ℝ × ℝ => c z.1 z.2) Omega)
    (hT : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × ℝ => (⟨c z.1 z.2,
        curveVelocity (fun s => c z.1 s) z.2⟩ : TangentBundle (𝓡 n) M)) Omega)
    {x t : ℝ} (hxt : (x, t) ∈ Omega) :
    MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun s => (⟨c x s, curveVelocity (fun y => c y s) x⟩ :
        TangentBundle (𝓡 n) M)) t ∧
      rampHorizontalCovariantDerivative D (fun s => c x s)
          (fun s => curveVelocity (fun y => c y s) x) t =
        rampHorizontalCovariantDerivative D (fun y => c y t)
          (fun y => curveVelocity (fun s => c y s) t) x := by
  let p := c x t
  let e := chartAt E p
  let U := Omega ∩ (fun z : ℝ × ℝ => c z.1 z.2) ⁻¹' e.source
  have hU : IsOpen U := hc.continuousOn.isOpen_inter_preimage hOmega e.open_source
  have hbase : c x t ∈ e.source := mem_chart_source E p
  have hz : (x, t) ∈ U := ⟨hxt, hbase⟩
  let q : ℝ × ℝ → E := fun z => e (c z.1 z.2)
  let R : ℝ × ℝ → E := fun z =>
    mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2) (curveVelocity (fun s => c z.1 s) z.2)
  have hq : ContDiffOn ℝ 1 q U :=
    (contMDiffOn_chart.comp (hc.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) 2 e e.source := contMDiffOn_chart
  have hpush := (hchart.contMDiffOn_tangentMapWithin (m := 1) (by norm_num)
    e.open_source.uniqueMDiffOn).comp (hT.mono inter_subset_left) (fun z hz => hz.2)
  have hR : ContDiffOn ℝ 1 R U := by
    have h := ((contMDiff_snd_tangentBundle_modelSpace (n := 1) E (𝓡 n)).comp_contMDiffOn
      hpush).contDiffOn
    apply h.congr
    intro z hz
    change mfderiv (𝓡 n) (𝓡 n) e (c z.1 z.2)
        (curveVelocity (fun s => c z.1 s) z.2) =
      mfderivWithin (𝓡 n) (𝓡 n) e e.source (c z.1 z.2)
        (curveVelocity (fun s => c z.1 s) z.2)
    rw [mfderivWithin_of_isOpen e.open_source hz.2]
  have hcAt (z : ℝ × ℝ) (hz : z ∈ U) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n)
        (fun z : ℝ × ℝ => c z.1 z.2) z :=
    (hc.contMDiffAt (hOmega.mem_nhds hz.1)).mdifferentiableAt (by norm_num)
  have hfst (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : ℝ => (y, z.2)) z.1 :=
    (differentiableAt_id.prodMk (differentiableAt_const z.2)).mdifferentiableAt
  have hsnd (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun s : ℝ => (z.1, s)) z.2 :=
    ((differentiableAt_const z.1).prodMk differentiableAt_id).mdifferentiableAt
  have htime (z : ℝ × ℝ) (hz : z ∈ U) :
      HasDerivAt (fun s => q (z.1, s)) (R z) z.2 :=
    hasDerivAt_chart_curve p (fun s => c z.1 s) z.2 hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.2 (hsnd z))
  have hspace (z : ℝ × ℝ) (hz : z ∈ U) :
      DifferentiableAt ℝ (fun y => q (y, z.2)) z.1 := by
    have hdq : DifferentiableAt ℝ q z :=
      (hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    have hline : DifferentiableAt ℝ (fun y : ℝ => (y, z.2)) z.1 :=
      differentiableAt_id.prodMk (differentiableAt_const z.2)
    exact hdq.comp z.1 (g := q) (f := fun y : ℝ => (y, z.2)) hline
  have hX (z : ℝ × ℝ) (hz : z ∈ U) :
      chartVectorField p (deriv (fun y => q (y, z.2)) z.1) (c z.1 z.2) =
        curveVelocity (fun y => c y z.2) z.1 :=
    chartVectorField_coordinate_velocity p (fun y => c y z.2) z.1 _ hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.1 (hfst z))
      (hspace z hz).hasDerivAt
  have hY (z : ℝ × ℝ) (hz : z ∈ U) :
      chartVectorField p (R z) (c z.1 z.2) = curveVelocity (fun s => c z.1 s) z.2 :=
    chartVectorField_coordinate_velocity p (fun s => c z.1 s) z.2 _ hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.2 (hsnd z)) (htime z hz)
  let V : Set ℝ := (fun s : ℝ => (x, s)) ⁻¹' U
  let W : Set ℝ := (fun y : ℝ => (y, t)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hW : IsOpen W := hU.preimage (continuous_id.prodMk continuous_const)
  let v : ℝ → E := fun s => deriv (fun y => q (y, s)) x
  let w : ℝ → E := fun y => R (y, t)
  have hdv (s : ℝ) (hs : s ∈ V) : HasDerivAt v (fderiv ℝ R (x, s) (1, 0)) s :=
    hasDerivAt_spatialDeriv_of_time_equation hU hq hR htime hs
  have hv : ContDiffOn ℝ 1 v V := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hV).mpr
    refine ⟨fun s hs => (hdv s hs).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    apply contDiffOn_zero.mpr
    have hRx : ContinuousOn (fun z : ℝ × ℝ => fderiv ℝ R z (1, 0)) U :=
      ((hR.fderiv_of_isOpen hU (m := 0) (by norm_num)).clm_apply
        (contDiffOn_const (c := ((1 : ℝ), (0 : ℝ))))).continuousOn
    have hcont := hRx.comp (s := V) (f := fun s : ℝ => (x, s))
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => hs)
    exact hcont.congr (fun s hs => (hdv s hs).deriv)
  have hw : ContDiffOn ℝ 1 w W :=
    hR.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy => hy)
  have hcTime : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun s => c x s) V :=
    (hc.mono inter_subset_left).comp
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn (fun _ hs => hs)
  have hXtime : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun s => (⟨c x s, curveVelocity (fun y => c y s) x⟩ :
        TangentBundle (𝓡 n) M)) V := by
    have h := (chartVectorField_param_contMDiff_one p v V hv).comp
      (contMDiffOn_id.prodMk hcTime) (fun s hs => ⟨hs, hs.2⟩)
    apply h.congr
    intro s hs
    exact congrArg (Bundle.TotalSpace.mk' E (c x s)) (hX (x, s) hs).symm
  refine ⟨(hXtime.contMDiffAt (hV.mem_nhds hz)).mdifferentiableAt (by norm_num), ?_⟩
  have hleft : rampHorizontalCovariantDerivative D (fun s => c x s)
        (fun s => curveVelocity (fun y => c y s) x) t =
      chartVectorField p (deriv v t) (c x t) +
        D.connection (chartVectorField p (v t)) (c x t) (curveVelocity (fun s => c x s) t) := by
    calc
      _ = rampHorizontalCovariantDerivative D (fun s => c x s)
          (fun s => chartVectorField p (v s) (c x s)) t :=
        M62.pullback_congr D (γ := fun s => c x s)
          (Y := fun s => curveVelocity (fun y => c y s) x)
          (Z := fun s => chartVectorField p (v s) (c x s)) (by
          filter_upwards [hV.mem_nhds hz] with s hs
          exact (hX (x, s) hs).symm)
      _ = _ := pullback_chart_field_of_contDiff_one D p (gamma := fun s => c x s) (x := t)
        (by simpa only [Function.comp_def] using (hcAt (x, t) hz).comp t (hsnd (x, t)))
        hbase hV hz v hv
  have hright : rampHorizontalCovariantDerivative D (fun y => c y t)
        (fun y => curveVelocity (fun s => c y s) t) x =
      chartVectorField p (deriv w x) (c x t) +
        D.connection (chartVectorField p (w x)) (c x t) (curveVelocity (fun y => c y t) x) := by
    calc
      _ = rampHorizontalCovariantDerivative D (fun y => c y t)
          (fun y => chartVectorField p (w y) (c y t)) x :=
        M62.pullback_congr D (γ := fun y => c y t)
          (Y := fun y => curveVelocity (fun s => c y s) t)
          (Z := fun y => chartVectorField p (w y) (c y t)) (by
          filter_upwards [hW.mem_nhds hz] with y hy
          exact (hY (y, t) hy).symm)
      _ = _ := pullback_chart_field_of_contDiff_one D p (gamma := fun y => c y t) (x := x)
        (by simpa only [Function.comp_def] using (hcAt (x, t) hz).comp x (hfst (x, t)))
        hbase hW hz w hw
  have hdw : HasDerivAt w (fderiv ℝ R (x, t) (1, 0)) x := by
    have hdR : DifferentiableAt ℝ R (x, t) :=
      (hR.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
    exact M08.coordinateSlice_fst_hasDerivAt R hdR
  have hfield (z : E) :=
    ((chartVectorField_smooth p z).contMDiffAt (e.open_source.mem_nhds hbase)).mdifferentiableAt
      (by simp)
  have htor := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero
    (hfield (w x)) (hfield (v t))
  rw [chartVectorField_bracket p (w x) (v t) (c x t) hbase] at htor
  have hconn := sub_eq_zero.mp htor
  rw [hleft, hright, (hdv t hz).deriv, hdw.deriv, ← hY (x, t) hz, ← hX (x, t) hz]
  exact congrArg (_ + ·) hconn

end PoincareConjecture.M63
