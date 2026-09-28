import PoincareConjecture.Proofs.M62.Sec19_1_PullbackRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 5000000 in



theorem flow_pullback_curvature_pair [T2Space M]
    (F : RicciFlow n M J) (c : ℝ → ℝ → M)
    (Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    {Omega : Set (ℝ × ℝ)} (hOmega : IsOpen Omega)
    (hTime : ∀ z ∈ Omega, z.2 ∈ interior J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) Omega)
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M)) Omega)
    {x t : ℝ} (hxt : (x, t) ∈ Omega) (Z : TangentSpace (𝓡 n) (c x t)) :
    (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative (F.connection t) (fun r => c x r)
          (fun r => rampHorizontalCovariantDerivative (F.connection r) (fun s => c s r)
            (fun s => Y (s, r)) x) t -
        rampHorizontalCovariantDerivative (F.connection t) (fun s => c s t)
          (fun s => rampHorizontalCovariantDerivative (F.connection t) (fun r => c s r)
            (fun r => Y (s, r)) t) x) Z =
      (let X := curveVelocity (n := n) (fun s => c s t) x;
       let U := curveVelocity (n := n) (fun r => c x r) t;
       let V := Y (x, t);
       let D := F.connection t;
       (F.metric t).inner (c x t) (D.curvature (c x t) U X V) Z -
         D.covariantTensorDerivative D.ricciEvaluation (c x t) ![X, V, Z] -
         D.covariantTensorDerivative D.ricciEvaluation (c x t) ![V, X, Z] +
         D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, X, V]) := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let cc : ℝ → ℝ → M := fun r s => c s r
  let YY : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (cc z.1 z.2) := fun z => Y (z.2, z.1)
  let O := Prod.swap ⁻¹' Omega
  have hO : IsOpen O := hOmega.preimage continuous_swap
  have hcc : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => cc z.1 z.2) O :=
    hc.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn (fun z hz => hz)
  have hYY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨cc z.1 z.2, YY z⟩ : TangentBundle (𝓡 n) M)) O :=
    hY.comp (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffOn (fun z hz => hz)
  let p := c x t
  let e := chartAt E p
  let U := O ∩ (fun z : ℝ × ℝ => cc z.1 z.2) ⁻¹' e.source
  have hU : IsOpen U := hcc.continuousOn.isOpen_inter_preimage hO e.open_source
  have hbase : p ∈ e.source := mem_chart_source E p
  have hz : (t, x) ∈ U := ⟨hxt, hbase⟩
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  let q : ℝ × ℝ → E := fun z => e (cc z.1 z.2)
  let W : ℝ × ℝ → E := fun z => mfderiv (𝓡 n) (𝓡 n) e (cc z.1 z.2) (YY z)
  let Gamma : ℝ × E → E →L[ℝ] E →L[ℝ] E :=
    fun z => M04.shiChartChristoffel (F.connection z.1) e z.2
  have hq : ContDiffOn ℝ ∞ q U :=
    (he.comp (hcc.mono inter_subset_left) (fun z hz => hz.2)).contDiffOn
  have hW : ContDiffOn ℝ ∞ W U := by
    have h := (PoincareConjecture.Proofs.M09.tangentChartPhase_contMDiffOn p).comp
      (hYY.mono inter_subset_left) (fun z hz => hz.2)
    exact h.contDiffOn.snd
  have hGamma : ContDiffOn ℝ ∞ Gamma (J ×ˢ e.target) := flow_chartChristoffel_smooth F p
  have hmap : MapsTo (fun z : ℝ × ℝ => (z.1, q z)) U (J ×ˢ e.target) :=
    fun z hz => ⟨interior_subset (hTime (z.2, z.1) hz.1), e.map_source hz.2⟩
  have hcAt (z : ℝ × ℝ) (hz : z ∈ U) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n) (fun z : ℝ × ℝ => cc z.1 z.2) z :=
    (hcc.contMDiffAt (hO.mem_nhds hz.1)).mdifferentiableAt (by simp)
  have hfst (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (r, z.2)) z.1 :=
    (differentiableAt_id.prodMk (differentiableAt_const z.2)).mdifferentiableAt
  have hsnd (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun s : ℝ => (z.1, s)) z.2 :=
    ((differentiableAt_const z.1).prodMk differentiableAt_id).mdifferentiableAt
  have hT (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareConjecture.Proofs.M09.chartVectorField p (M08.coordinatePartialS q z) (cc z.1 z.2) =
        curveVelocity (fun r => cc r z.2) z.1 :=
    PoincareConjecture.Proofs.M09.chartVectorField_coordinate_velocity p (fun r => cc r z.2) z.1
      (M08.coordinatePartialS q z) hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.1 (hfst z))
      (M08.coordinateSlice_fst_hasDerivAt q
        ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
  have hX (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareConjecture.Proofs.M09.chartVectorField p (M08.coordinatePartialU q z) (cc z.1 z.2) =
        curveVelocity (fun s => cc z.1 s) z.2 :=
    PoincareConjecture.Proofs.M09.chartVectorField_coordinate_velocity p (fun s => cc z.1 s) z.2
      (M08.coordinatePartialU q z) hz.2
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.2 (hsnd z))
      (M08.coordinateSlice_snd_hasDerivAt q
        ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)))
  have hWvalue (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareConjecture.Proofs.M09.chartVectorField p (W z) (cc z.1 z.2) = YY z :=
    PoincareConjecture.Proofs.M09.chartVectorField_differential p _ _ hz.2
  have htime (A : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (cc z.1 z.2))
      (V : ℝ × ℝ → E) (hV : ContDiffOn ℝ ∞ V U)
      (hvalue : ∀ z ∈ U, PoincareConjecture.Proofs.M09.chartVectorField p (V z) (cc z.1 z.2) = A z)
      (z : ℝ × ℝ) (hz : z ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) e (cc z.1 z.2)
        (rampHorizontalCovariantDerivative (F.connection z.1) (fun r => cc r z.2)
          (fun r => A (r, z.2)) z.1) = M08.coordinateCovariantS Gamma q V z := by
    let B := (fun r : ℝ => (r, z.2)) ⁻¹' U
    have hB : IsOpen B := hU.preimage (continuous_id.prodMk continuous_const)
    have hcongr := pullback_congr (F.connection z.1) (γ := fun r => cc r z.2)
      (Y := fun r => A (r, z.2))
      (Z := fun r => PoincareConjecture.Proofs.M09.chartVectorField p (V (r, z.2)) (cc r z.2))
      (x := z.1) (by
        filter_upwards [hB.mem_nhds hz] with r hr
        exact (hvalue (r, z.2) hr).symm)
    rw [hcongr, pullback_chart_field_coordinates (F.connection z.1) p
      (gamma := fun r => cc r z.2) (x := z.1)
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.1 (hfst z))
      hz.2 hB hz (fun r => V (r, z.2))
      (hV.comp (contDiffOn_id.prodMk contDiffOn_const) (fun r hr => hr))]
    rw [(M08.coordinateSlice_fst_hasDerivAt V
      ((hV.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv]
    rw [← hT z hz]
    erw [M04.shiChartField_duality he hi hz.2]
    rfl
  have hspace (A : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (cc z.1 z.2))
      (V : ℝ × ℝ → E) (hV : ContDiffOn ℝ ∞ V U)
      (hvalue : ∀ z ∈ U, PoincareConjecture.Proofs.M09.chartVectorField p (V z) (cc z.1 z.2) = A z)
      (z : ℝ × ℝ) (hz : z ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) e (cc z.1 z.2)
        (rampHorizontalCovariantDerivative (F.connection z.1) (fun s => cc z.1 s)
          (fun s => A (z.1, s)) z.2) = M08.coordinateCovariantU Gamma q V z := by
    let B := (fun s : ℝ => (z.1, s)) ⁻¹' U
    have hB : IsOpen B := hU.preimage (continuous_const.prodMk continuous_id)
    have hcongr := pullback_congr (F.connection z.1) (γ := fun s => cc z.1 s)
      (Y := fun s => A (z.1, s))
      (Z := fun s => PoincareConjecture.Proofs.M09.chartVectorField p (V (z.1, s)) (cc z.1 s))
      (x := z.2) (by
        filter_upwards [hB.mem_nhds hz] with s hs
        exact (hvalue (z.1, s) hs).symm)
    rw [hcongr, pullback_chart_field_coordinates (F.connection z.1) p
      (gamma := fun s => cc z.1 s) (x := z.2)
      (by simpa only [Function.comp_def] using (hcAt z hz).comp z.2 (hsnd z))
      hz.2 hB hz (fun s => V (z.1, s))
      (hV.comp (contDiffOn_const.prodMk contDiffOn_id) (fun s hs => hs))]
    rw [(M08.coordinateSlice_snd_hasDerivAt V
      ((hV.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))).deriv]
    rw [← hX z hz]
    erw [M04.shiChartField_duality he hi hz.2]
    rfl
  let Yx := fun z : ℝ × ℝ => rampHorizontalCovariantDerivative (F.connection z.1)
    (fun s => cc z.1 s) (fun s => YY (z.1, s)) z.2
  let Yt := fun z : ℝ × ℝ => rampHorizontalCovariantDerivative (F.connection z.1)
    (fun r => cc r z.2) (fun r => YY (r, z.2)) z.1
  have hWx := M08.coordinateCovariantU_contDiffOn hU Gamma q W hGamma hq hW hmap
  have hWt := M08.coordinateCovariantS_contDiffOn hU Gamma q W hGamma hq hW hmap
  have hYx (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareConjecture.Proofs.M09.chartVectorField p
        (M08.coordinateCovariantU Gamma q W z) (cc z.1 z.2) = Yx z := by
    rw [← hspace YY W hW hWvalue z hz]
    exact PoincareConjecture.Proofs.M09.chartVectorField_differential p _ _ hz.2
  have hYt (z : ℝ × ℝ) (hz : z ∈ U) :
      PoincareConjecture.Proofs.M09.chartVectorField p
        (M08.coordinateCovariantS Gamma q W z) (cc z.1 z.2) = Yt z := by
    rw [← htime YY W hW hWvalue z hz]
    exact PoincareConjecture.Proofs.M09.chartVectorField_differential p _ _ hz.2
  have hGammaAt : DifferentiableAt ℝ Gamma (t, q (t, x)) :=
    (hGamma.contDiffAt (prod_mem_nhds_iff.mpr
      ⟨mem_interior_iff_mem_nhds.mp (hTime (x, t) hxt),
        e.open_target.mem_nhds (e.map_source hbase)⟩)).differentiableAt (by simp)
  have hGammaSpace : HasFDerivAt (M04.shiChartChristoffel (F.connection t) e)
      ((fderiv ℝ Gamma (t, q (t, x))).comp
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E))) (q (t, x)) := by
    exact hGammaAt.hasFDerivAt.comp (q (t, x))
      ((hasFDerivAt_const t (q (t, x))).prodMk (hasFDerivAt_id (q (t, x))))
  have hGammaDer (v : E) :
      fderiv ℝ (M04.shiChartChristoffel (F.connection t) e) (q (t, x)) v =
        fderiv ℝ Gamma (t, q (t, x)) (0, v) := by
    rw [hGammaSpace.fderiv]
    rfl
  have hcomm := M08.coordinateCovariant_commutator Gamma q W
    (hq.contDiffAt (hU.mem_nhds hz)) (hW.contDiffAt (hU.mem_nhds hz)) hGammaAt
  have hR := M04.shiChart_curvature_formula (F.connection t) he hi (e.map_source hbase)
    (M08.coordinatePartialS q (t, x)) (M08.coordinatePartialU q (t, x)) (W (t, x))
  rw [← M04.shiChartField_at_inverse he hi (e.map_source hbase),
    ← M04.shiChartField_at_inverse he hi (e.map_source hbase),
    ← M04.shiChartField_at_inverse he hi (e.map_source hbase), e.left_inv hbase] at hR
  change mfderiv (𝓡 n) (𝓡 n) e p
    ((F.connection t).curvature p
      (PoincareConjecture.Proofs.M09.chartVectorField p (M08.coordinatePartialS q (t, x)) p)
      (PoincareConjecture.Proofs.M09.chartVectorField p (M08.coordinatePartialU q (t, x)) p)
      (PoincareConjecture.Proofs.M09.chartVectorField p (W (t, x)) p)) = _ at hR
  rw [hT (t, x) hz, hX (t, x) hz, hWvalue (t, x) hz, hGammaDer, hGammaDer] at hR
  let Ccoord : E := mfderiv (𝓡 n) (𝓡 n) e p
    ((F.connection t).curvature p (curveVelocity (fun r => cc r x) t)
      (curveVelocity (fun s => cc t s) x) (YY (t, x)))
  let B := fderiv ℝ Gamma (t, q (t, x)) (1, 0)
    (M08.coordinatePartialU q (t, x)) (W (t, x))
  have hRcoord : Ccoord =
      (((fderiv ℝ Gamma (t, q (t, x))) (0, M08.coordinatePartialS q (t, x)))
          (M08.coordinatePartialU q (t, x))) (W (t, x)) -
        (((fderiv ℝ Gamma (t, q (t, x))) (0, M08.coordinatePartialU q (t, x)))
          (M08.coordinatePartialS q (t, x))) (W (t, x)) +
        ((Gamma (t, q (t, x))) (M08.coordinatePartialS q (t, x)))
          (((Gamma (t, q (t, x))) (M08.coordinatePartialU q (t, x))) (W (t, x))) -
      ((Gamma (t, q (t, x))) (M08.coordinatePartialU q (t, x)))
        (((Gamma (t, q (t, x))) (M08.coordinatePartialS q (t, x))) (W (t, x))) := by
    simpa only [Ccoord, Gamma, q, p, cc] using hR
  have hcoord : M08.coordinateCovariantS Gamma q (M08.coordinateCovariantU Gamma q W) (t, x) -
      M08.coordinateCovariantU Gamma q (M08.coordinateCovariantS Gamma q W) (t, x) =
      Ccoord + B := by
    calc
      _ = -(M08.coordinateCovariantU Gamma q (M08.coordinateCovariantS Gamma q W) (t, x) -
          M08.coordinateCovariantS Gamma q (M08.coordinateCovariantU Gamma q W) (t, x)) := by
        simp only [sub_eq_add_neg, neg_add]
        abel
      _ = _ := by
        rw [hcomm, hRcoord]
        dsimp only [B, Gamma, q, p, cc]
        abel
  let L : E →L[ℝ] ℝ := ((F.metric t).inner p Z).comp
    (mfderiv (𝓡 n) (𝓡 n) e p).inverse
  have hL (V : TangentSpace (𝓡 n) p) :
      L (mfderiv (𝓡 n) (𝓡 n) e p V) = (F.metric t).inner p V Z := by
    change (F.metric t).inner p Z ((mfderiv (𝓡 n) (𝓡 n) e p).inverse
      (mfderiv (𝓡 n) (𝓡 n) e p V)) = _
    rw [(M04.shiChart_mfderiv_isInvertible he hi hbase).inverse_apply_self]
    exact (F.metric t).symm p Z V
  have hGt : HasDerivAt (fun r => Gamma (r, q (t, x)))
      (fderiv ℝ Gamma (t, q (t, x)) (1, 0)) t :=
    by
      change HasDerivAt (Gamma ∘ fun r : ℝ => (r, q (t, x)))
        (fderiv ℝ Gamma (t, q (t, x)) (1, 0)) t
      simpa only [id_eq] using hGammaAt.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t (q (t, x))))
  have hGB : HasDerivAt (fun r => Gamma (r, q (t, x))
      (M08.coordinatePartialU q (t, x)) (W (t, x))) B t := by
    simpa only [map_zero, zero_add, add_zero] using
      (hGt.clm_apply (hasDerivAt_const t (M08.coordinatePartialU q (t, x)))).clm_apply
        (hasDerivAt_const t (W (t, x)))
  have hpaired := L.hasFDerivAt.comp_hasDerivAt t hGB
  have hvariation := hasDerivAt_flow_chartChristoffel_pair F p (hTime (x, t) hxt)
    hbase (M08.coordinatePartialU q (t, x)) (W (t, x))
      (mfderiv (𝓡 n) (𝓡 n) e p Z)
  rw [PoincareConjecture.Proofs.M09.chartVectorField_differential p p Z hbase] at hvariation
  have hvariation' : HasDerivAt (fun r => L (Gamma (r, q (t, x))
      (M08.coordinatePartialU q (t, x)) (W (t, x)))) _ t :=
    hvariation.congr_of_eventuallyEq (Eventually.of_forall fun r =>
      (F.metric t).symm p Z _)
  have hB := hpaired.unique hvariation'
  dsimp only at hB
  rw [hX (t, x) hz, hWvalue (t, x) hz] at hB
  have hfinal := congrArg L hcoord
  rw [map_sub, map_add, hL, hB] at hfinal
  rw [← htime Yx _ hWx hYx (t, x) hz, ← hspace Yt _ hWt hYt (t, x) hz,
    hL, hL] at hfinal
  change (F.metric t).inner p (_ - _) Z = _
  rw [map_sub, sub_apply]
  convert hfinal using 1
  all_goals
    dsimp only [cc, YY, Yx, Yt, p]
    ring

end PoincareConjecture.M62
