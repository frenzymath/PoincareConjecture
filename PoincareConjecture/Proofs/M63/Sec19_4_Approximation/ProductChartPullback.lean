import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductConnection
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackTorsion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {circumference : ℝ} {C : M62.CircleGeometry circumference}

theorem productChartField_param_smooth (P : M62.CircleProductCharts C n M)
    (p : M) (v : ℝ → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hv : ContDiffOn ℝ ∞ v U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 (n + 1))) (𝓡 (n + 1)).tangent ∞
      (fun z : ℝ × P.Point =>
        (⟨z.2, P.productChartField p (v z.1) r z.2⟩ :
          TangentBundle (𝓡 (n + 1)) P.Point))
      (U ×ˢ {q : P.Point | q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source}) := by
  let := P.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞ (Prod.snd : P.Point → C.Point) :=
    contMDiff_snd.comp P.to_product_smooth
  have hsplit (q : P.Point) (V : TangentSpace ((𝓡 n).prod (𝓡 1)) q) :
      P.split q (mfderiv (M' := P.Point) ((𝓡 n).prod (𝓡 1)) (𝓡 (n + 1))
        (id : M × C.Point → P.Point) q V) = (V.1, V.2) := by
    apply Prod.ext
    · rw [P.split_space]
      have h := mfderiv_comp_apply (f := (id : M × C.Point → P.Point))
        (g := (Prod.fst : P.Point → M)) q (hfst.mdifferentiableAt (by simp))
        (P.from_product_smooth.mdifferentiableAt (by simp)) V
      simpa +instances only [Function.comp_def, id_eq, mfderiv_fst,
        ContinuousLinearMap.coe_fst'] using! h.symm
    · rw [P.split_circle]
      have h := mfderiv_comp_apply (f := (id : M × C.Point → P.Point))
        (g := (Prod.snd : P.Point → C.Point)) q (hsnd.mdifferentiableAt (by simp))
        (P.from_product_smooth.mdifferentiableAt (by simp)) V
      simpa +instances only [Function.comp_def, id_eq, mfderiv_snd,
        ContinuousLinearMap.coe_snd'] using! h.symm
  intro z hz
  have hX : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 (n + 1))) (𝓡 n).tangent ∞
      (fun w : ℝ × P.Point =>
        (⟨w.2.1, chartVectorField p (v w.1) w.2.1⟩ : TangentBundle (𝓡 n) M)) z :=
    ((chartVectorField_param_smooth p v U hv).contMDiffAt
      ((hU.prod (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source).mem_nhds
        (show (z.1, z.2.1) ∈ U ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) p).source from
          ⟨hz.1, hz.2⟩))).comp z
      (contMDiffAt_fst.prodMk ((hfst z.2).comp z contMDiffAt_snd))
  have hcircle : ContMDiffAt (𝓡 1) (𝓡 1).tangent ∞
      (fun q : C.Point => (⟨q, r • C.frame q⟩ : TangentBundle (𝓡 1) C.Point)) z.2.2 :=
    ((M62.circle_identities C).frame_smooth z.2.2).const_smul_section (a := r)
  have hprod : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 (n + 1)))
      ((𝓡 n).prod (𝓡 1)).tangent ∞
      (fun w : ℝ × P.Point =>
        (⟨w.2, (chartVectorField p (v w.1) w.2.1, r • C.frame w.2.2)⟩ :
          TangentBundle ((𝓡 n).prod (𝓡 1)) (M × C.Point))) z :=
    contMDiff_equivTangentBundleProd_symm.contMDiffAt.comp z
      (hX.prodMk (hcircle.comp z ((hsnd z.2).comp z contMDiffAt_snd)))
  have h := (P.from_product_smooth.contMDiff_tangentMap (m := ∞)
    (by simp)).contMDiffAt.comp z hprod
  apply ContMDiffAt.contMDiffWithinAt
  apply h.congr_of_eventuallyEq
  filter_upwards [] with w
  dsimp only [Function.comp_apply, id_eq, tangentMap]
  rw [TotalSpace.mk_inj]
  apply (P.split w.2).injective
  erw [hsplit]
  exact P.productChartField_split p (v w.1) r w.2

theorem circleProduct_pullback_chart_field
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (P : M62.CircleProductCharts C n M)
    (G : RiemannianMetric (n + 1) P.Point) (DG : LeviCivitaData G)
    (hG : ∀ (q : P.Point) (V W : TangentSpace (𝓡 (n + 1)) q),
      G.inner q V W = g.inner q.1 (P.split q V).1 (P.split q W).1 +
        C.metricOnPoints.inner q.2 (P.split q V).2 (P.split q W).2)
    (p : M) {gamma : ℝ → P.Point} {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma x)
    (hsource : (gamma x).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {U : Set ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (v : ℝ → EuclideanSpace ℝ (Fin n)) (hv : ContDiffOn ℝ ∞ v U) (r : ℝ) :
    P.split (gamma x) (rampHorizontalCovariantDerivative DG gamma
      (fun s => P.productChartField p (v s) r (gamma s)) x) =
        (rampHorizontalCovariantDerivative D (fun s => (gamma s).1)
          (fun s => chartVectorField p (v s) (gamma s).1) x, 0) := by
  let := P.chartedSpace
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 1) : C.Point → Type _) :=
    ⟨C.metricOnPoints.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.Point → Type _) :=
    ⟨G.toRiemannianMetric⟩
  let W := fun s q => P.productChartField p (v s) r q
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.Point → M) :=
    contMDiff_fst.comp P.to_product_smooth
  have hopen : IsOpen {q : P.Point |
      q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source} :=
    (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.preimage hfst.continuous
  have hW : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 (n + 1))) (𝓡 (n + 1)).tangent
      (fun z : ℝ × P.Point => (⟨z.2, W z.1 z.2⟩ :
        TangentBundle (𝓡 (n + 1)) P.Point)) (x, gamma x) :=
    ((productChartField_param_smooth P p v r hU hv).contMDiffAt
      ((hU.prod hopen).mem_nhds (show (x, gamma x) ∈ U ×ˢ
        {q : P.Point | q.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source} from
          ⟨hx, hsource⟩))).mdifferentiableAt (by simp)
  let L := (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p)
    (gamma x).1).inverse
  have hvx : DifferentiableAt ℝ v x :=
    ((hv x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have htime : HasDerivAt (fun s => W s (gamma x))
      (P.productChartField p (deriv v x) 0 (gamma x)) x := by
    have hbase := L.hasFDerivAt.comp_hasDerivAt x hvx.hasDerivAt
    have hp := hbase.prodMk (hasDerivAt_const x (r • C.frame (gamma x).2))
    have h := (P.split (gamma x)).symm.hasFDerivAt.comp_hasDerivAt x hp
    simpa +instances only [W, M62.CircleProductCharts.productChartField, chartVectorField,
      VectorField.mpullback, zero_smul, L, Function.comp_def] using! h
  have heq := (M62.hasDerivAt_fixedPointTimeDerivative W (gamma x) x hW).unique htime
  have hbase : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => (gamma s).1) x :=
    (hfst.mdifferentiableAt (by simp)).comp x hgamma
  have hvelocity : (P.split (gamma x) (curveVelocity gamma x)).1 =
      curveVelocity (fun s => (gamma s).1) x := by
    rw [P.split_space]
    exact (mfderiv_comp_apply (f := gamma) (g := (Prod.fst : P.Point → M)) x
      (hfst.mdifferentiableAt (by simp)) hgamma 1).symm
  obtain ⟨u, s, hus⟩ := P.productChartField_exists p (gamma x) hsource
    (curveVelocity gamma x)
  have hu : chartVectorField p u (gamma x).1 =
      curveVelocity (fun s => (gamma s).1) x := by
    rw [← hus, P.productChartField_split] at hvelocity
    exact hvelocity
  have hconn := M62.circleProduct_chart_connection g D C P G DG hG
    p u (v x) s r (gamma x) hsource
  rw [hus, hu] at hconn
  rw [M62.pullback_parametric_field DG hgamma W hW, heq, map_add,
    P.productChartField_split, hconn, M62.pullback_chart_field D p hbase hsource hU hx v hv]
  simp only [zero_smul, Prod.mk_add_mk, add_zero]

end PoincareConjecture.M63
