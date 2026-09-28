import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1ChartPullback
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddingHessianVector
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicConnection
import Mathlib.Analysis.Calculus.Deriv.Mul










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ ι




theorem hasDerivAt_embedding_pushforward_of_contMDiffAt_one
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) {gamma : ℝ → M} {x : ℝ}
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma x)
    (Y : (s : ℝ) → TangentSpace (𝓡 n) (gamma s))
    (hY : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 n) M)) x) :
    HasDerivAt (fun s => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma s) (Y s) : W))
      (HAdd.hAdd (α := W) (β := W) (γ := W)
        (coordinateHessian D e (gamma x) (curveVelocity gamma x) (Y x))
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma x)
          (rampHorizontalCovariantDerivative D gamma Y x))) x := by
  obtain ⟨Vg, hVg, hg⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by norm_num)).mp hgamma
  obtain ⟨VY, hVY, hYon⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by norm_num)).mp hY
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hVg hVY)
  have hgO := hg.mono (hOsub.trans inter_subset_left)
  have hYO := hYon.mono (hOsub.trans inter_subset_right)
  let p := gamma x
  let c := chartAt E p
  let U := O ∩ gamma ⁻¹' c.source
  have hU : IsOpen U := hgO.continuousOn.isOpen_inter_preimage hO c.open_source
  have hx : x ∈ U := ⟨hxO, mem_chart_source E p⟩
  have hgU : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma U := hgO.mono inter_subset_left
  let z : ℝ → E := fun r => c (gamma r)
  let w : ℝ → E := fun r => mfderiv (𝓡 n) (𝓡 n) c (gamma r) (Y r)
  let f : E → W := e ∘ c.symm
  have hz : ContDiffOn ℝ 1 z U :=
    (contMDiffOn_chart.comp hgU (fun _ hr => hr.2)).contDiffOn
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) 2 c c.source := contMDiffOn_chart
  have hpushField := (hchart.contMDiffOn_tangentMapWithin (m := 1) (by norm_num)
    c.open_source.uniqueMDiffOn).comp (hYO.mono inter_subset_left) (fun _ hr => hr.2)
  have hw : ContDiffOn ℝ 1 w U := by
    have h := ((contMDiff_snd_tangentBundle_modelSpace (n := 1) E (𝓡 n)).comp_contMDiffOn
      hpushField).contDiffOn
    apply h.congr
    intro r hr
    change mfderiv (𝓡 n) (𝓡 n) c (gamma r) (Y r) =
      mfderivWithin (𝓡 n) (𝓡 n) c c.source (gamma r) (Y r)
    rw [mfderivWithin_of_isOpen c.open_source hr.2]
  have hfield (r : ℝ) (hr : r ∈ U) :
      chartVectorField p (w r) (gamma r) = Y r := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) c (gamma r)).IsInvertible :=
      ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hr.2, rfl⟩
    exact hi.inverse_apply_self (Y r)
  have hdz : HasDerivAt z (deriv z x) x :=
    ((hz.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hdw : HasDerivAt w (deriv w x) x :=
    ((hw.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hvel : chartVectorField p (deriv z x) (gamma x) = curveVelocity gamma x :=
    chartVectorField_coordinate_velocity p gamma x (deriv z x) hx.2
      (hgamma.mdifferentiableAt (by norm_num)) hdz
  have hf : ContDiffOn ℝ ∞ f c.target :=
    (he.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓡 n) (x := p))).contDiffOn
  have hpush (r : ℝ) (hr : r ∈ U) (v : E) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma r) (chartVectorField p v (gamma r)) =
        fderiv ℝ f (z r) v := by
    have htarget : z r ∈ c.target := c.map_source hr.2
    have hchain := mfderiv_comp (z r) (he.mdifferentiable (by simp)).mdifferentiableAt
      ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm htarget)
    rw [mfderiv_eq_fderiv] at hchain
    have hv := congrArg (fun L : E →L[ℝ] W => L v) hchain
    change fderiv ℝ f (z r) v =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c.symm (z r))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (z r) v) at hv
    rw [← chartVectorField_at_inverse p v (z r) htarget, c.left_inv hr.2] at hv
    exact hv.symm
  have hlocal : (fun r => mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma r) (Y r)) =ᶠ[𝓝 x]
      (fun r => fderiv ℝ f (z r) (w r)) := by
    filter_upwards [hU.mem_nhds hx] with r hr
    rw [← hfield r hr]
    exact hpush r hr (w r)
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (z x)) (z x) :=
    (((hf.contDiffAt (c.open_target.mem_nhds (c.map_source hx.2))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hd := ((hD.comp_hasDerivAt x hdz).clm_apply hdw).congr_of_eventuallyEq hlocal
  have hconn := chartVectorField_coordinateChristoffel D p (z x)
    (c.map_source hx.2) (deriv z x) (w x)
  have hbase : c.symm (z x) = gamma x := c.left_inv hx.2
  rw [hbase, hvel] at hconn
  have hcov : rampHorizontalCovariantDerivative D gamma Y x =
      chartVectorField p (deriv w x +
        coordinateChristoffel (g.pullbackCoefficients c.symm) (z x) (deriv z x) (w x))
        (gamma x) := by
    calc
      _ = rampHorizontalCovariantDerivative D gamma
          (fun r => chartVectorField p (w r) (gamma r)) x :=
        M62.pullback_congr D (γ := gamma) (Y := Y)
          (Z := fun r => chartVectorField p (w r) (gamma r)) (by
          filter_upwards [hU.mem_nhds hx] with r hr
          exact (hfield r hr).symm)
      _ = chartVectorField p (deriv w x) (gamma x) +
          D.connection (chartVectorField p (w x)) (gamma x) (curveVelocity gamma x) :=
        pullback_chart_field_of_contDiff_one D p (hgamma.mdifferentiableAt (by norm_num))
          hx.2 hU hx w hw
      _ = _ := by
        rw [← hconn]
        simp only [chartVectorField, VectorField.mpullback, map_add, c]
  have hhess := coordinateHessian_eq_chart D he p (gamma x) hx.2 (deriv z x) (w x)
  dsimp only at hhess
  rw [hvel, hfield x hx] at hhess
  convert! hd using 1
  rw [hhess, hcov, hpush x hx, map_add]
  abel

end PoincareConjecture.M63
