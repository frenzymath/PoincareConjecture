import PoincareConjecture.Proofs.M62.Sec19_1_ParametricRestriction
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackAlgebra
import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M08.SecondVariationCoordinates

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Filter
open PoincareConjecture.Proofs.M09

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullback_chart_field {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) {γ : ℝ → M} {x : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ x)
    (hsource : γ x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {U : Set ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (v : ℝ → EuclideanSpace ℝ (Fin n)) (hv : ContDiffOn ℝ ∞ v U) :
    rampHorizontalCovariantDerivative D γ (fun r ↦ chartVectorField p (v r) (γ r)) x =
      chartVectorField p (deriv v x) (γ x) +
        D.connection (chartVectorField p (v x)) (γ x) (curveVelocity γ x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let W := fun r q ↦ chartVectorField p (v r) q
  have hW : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
      (fun z : ℝ × M ↦ (⟨z.2, W z.1 z.2⟩ : TangentBundle (𝓡 n) M)) (x, γ x) :=
    ((chartVectorField_param_smooth p v U hv).contMDiffAt
      (prod_mem_nhds (hU.mem_nhds hx)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hsource))).mdifferentiableAt
      (by simp)
  let L := (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) (γ x)).inverse
  have htime : HasDerivAt (fun r ↦ W r (γ x)) (chartVectorField p (deriv v x) (γ x)) x :=
    L.hasFDerivAt.comp_hasDerivAt x
      (((hv x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have heq := (hasDerivAt_fixedPointTimeDerivative W (γ x) x hW).unique htime
  rw [pullback_parametric_field D hγ W hW, heq]

theorem pullback_velocity_commute {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (c : ℝ → ℝ → M)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hc : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ (fun z : ℝ × ℝ ↦ c z.1 z.2) Ω)
    {x t : ℝ} (hxt : (x, t) ∈ Ω) :
    rampHorizontalCovariantDerivative D (fun s ↦ c x s)
        (fun s ↦ curveVelocity (fun y ↦ c y s) x) t =
      rampHorizontalCovariantDerivative D (fun y ↦ c y t)
        (fun y ↦ curveVelocity (fun s ↦ c y s) t) x := by
  let p := c x t
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let U := Ω ∩ (fun z : ℝ × ℝ ↦ c z.1 z.2) ⁻¹' e.source
  have hU : IsOpen U := hc.continuousOn.isOpen_inter_preimage hΩ e.open_source
  have hbase : c x t ∈ e.source := mem_chart_source _ p
  have hz : (x, t) ∈ U := ⟨hxt, hbase⟩
  let q : ℝ × ℝ → EuclideanSpace ℝ (Fin n) := fun z ↦ e (c z.1 z.2)
  have hq : ContDiffOn ℝ ∞ q U :=
    (contMDiffOn_chart.comp (hc.mono Set.inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  have hcAt (z : ℝ × ℝ) (hz : z ∈ U) :
      MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) (fun z : ℝ × ℝ ↦ c z.1 z.2) z :=
    ((hc z hz.1).contMDiffAt (hΩ.mem_nhds hz.1)).mdifferentiableAt (by simp)
  have hfst (z : ℝ × ℝ) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun r : ℝ ↦ (r, z.2)) z.1 :=
    (differentiableAt_id.prodMk (differentiableAt_const z.2)).mdifferentiableAt
  have hsnd (z : ℝ × ℝ) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun r : ℝ ↦ (z.1, r)) z.2 :=
    ((differentiableAt_const z.1).prodMk differentiableAt_id).mdifferentiableAt
  have hX (z : ℝ × ℝ) (hz : z ∈ U) :
      chartVectorField p (M08.coordinatePartialS q z) (c z.1 z.2) =
        curveVelocity (fun r ↦ c r z.2) z.1 :=
    chartVectorField_coordinate_velocity p (fun r ↦ c r z.2) z.1
      (M08.coordinatePartialS q z) hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.1 (hfst z))
      (M08.coordinateSlice_fst_hasDerivAt q
        (((hq z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
  have hT (z : ℝ × ℝ) (hz : z ∈ U) :
      chartVectorField p (M08.coordinatePartialU q z) (c z.1 z.2) =
        curveVelocity (fun r ↦ c z.1 r) z.2 :=
    chartVectorField_coordinate_velocity p (fun r ↦ c z.1 r) z.2
      (M08.coordinatePartialU q z) hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.2 (hsnd z))
      (M08.coordinateSlice_snd_hasDerivAt q
        (((hq z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
  let V := (fun r : ℝ ↦ (x, r)) ⁻¹' U
  let W := (fun r : ℝ ↦ (r, t)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hW : IsOpen W := hU.preimage (continuous_id.prodMk continuous_const)
  let v : ℝ → EuclideanSpace ℝ (Fin n) := fun r ↦ M08.coordinatePartialS q (x, r)
  let w : ℝ → EuclideanSpace ℝ (Fin n) := fun r ↦ M08.coordinatePartialU q (r, t)
  have hA := M08.coordinatePartialS_contDiffOn hU q hq
  have hB := M08.coordinatePartialU_contDiffOn hU q hq
  have hv : ContDiffOn ℝ ∞ v V :=
    hA.comp (contDiffOn_const.prodMk contDiffOn_id) (fun r hr ↦ hr)
  have hw : ContDiffOn ℝ ∞ w W :=
    hB.comp (contDiffOn_id.prodMk contDiffOn_const) (fun r hr ↦ hr)
  have hleft : rampHorizontalCovariantDerivative D (fun s ↦ c x s)
        (fun s ↦ curveVelocity (fun y ↦ c y s) x) t =
      chartVectorField p (deriv v t) (c x t) +
        D.connection (chartVectorField p (v t)) (c x t) (curveVelocity (fun s ↦ c x s) t) := by
    calc
      _ = rampHorizontalCovariantDerivative D (fun s ↦ c x s)
          (fun s ↦ chartVectorField p (v s) (c x s)) t := pullback_congr D
          (γ := fun s ↦ c x s) (Y := fun s ↦ curveVelocity (fun y ↦ c y s) x)
          (Z := fun s ↦ chartVectorField p (v s) (c x s)) (x := t) (by
            filter_upwards [hV.mem_nhds hz] with s hs
            exact (hX (x, s) hs).symm)
      _ = _ := pullback_chart_field D p (γ := fun s ↦ c x s) (x := t)
        (by simpa only [Function.comp_def] using (hcAt (x, t) hz).comp t (hsnd (x, t)))
        hbase hV hz v hv
  have hright : rampHorizontalCovariantDerivative D (fun y ↦ c y t)
        (fun y ↦ curveVelocity (fun s ↦ c y s) t) x =
      chartVectorField p (deriv w x) (c x t) +
        D.connection (chartVectorField p (w x)) (c x t) (curveVelocity (fun y ↦ c y t) x) := by
    calc
      _ = rampHorizontalCovariantDerivative D (fun y ↦ c y t)
          (fun y ↦ chartVectorField p (w y) (c y t)) x := pullback_congr D
          (γ := fun y ↦ c y t) (Y := fun y ↦ curveVelocity (fun s ↦ c y s) t)
          (Z := fun y ↦ chartVectorField p (w y) (c y t)) (x := x) (by
            filter_upwards [hW.mem_nhds hz] with y hy
            exact (hT (y, t) hy).symm)
      _ = _ := pullback_chart_field D p (γ := fun y ↦ c y t) (x := x)
        (by simpa only [Function.comp_def] using (hcAt (x, t) hz).comp x (hfst (x, t)))
        hbase hW hz w hw
  have hdv : deriv v t = M08.coordinatePartialU (M08.coordinatePartialS q) (x, t) :=
    (M08.coordinateSlice_snd_hasDerivAt (M08.coordinatePartialS q)
      (((hA (x, t) hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv
  have hdw : deriv w x = M08.coordinatePartialS (M08.coordinatePartialU q) (x, t) :=
    (M08.coordinateSlice_fst_hasDerivAt (M08.coordinatePartialU q)
      (((hB (x, t) hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv
  have hfield (a : EuclideanSpace ℝ (Fin n)) :=
    ((chartVectorField_smooth p a).contMDiffAt (e.open_source.mem_nhds hbase)).mdifferentiableAt
      (by simp)
  have htor := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero (hfield (w x)) (hfield (v t))
  rw [chartVectorField_bracket p (w x) (v t) (c x t) hbase] at htor
  have hconn := sub_eq_zero.mp htor
  rw [hleft, hright, hdv, hdw,
    M08.coordinatePartials_commute q ((hq (x, t) hz).contDiffAt (hU.mem_nhds hz)),
    ← hT (x, t) hz, ← hX (x, t) hz]
  exact congrArg (_ + ·) hconn

end PoincareConjecture.M62
