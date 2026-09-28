import PoincareConjecture.Proofs.M10.GramCalculus
import PoincareConjecture.Proofs.M10.CoordinateGradient
import PoincareConjecture.Proofs.M10.PreferredHessian
import PoincareConjecture.Proofs.M10.BackwardMetricDerivative

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem coordinate_terminal_pairing_eventually (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (q₀ : M)
    (z : TangentSpace (𝓡 n) p × ℝ)
    (hreg : z ∈ G.toLExponentialFamily.regularDomain)
    (hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    ∀ᶠ V in 𝓝 z.1,
      fderiv ℝ ((fun x ↦ reducedLength F T p x z.2) ∘ (extChartAt (𝓡 n) q₀).symm)
          (endpointCoordinates G q₀ (V, z.2)) v =
        coordinateBackwardMetric F T q₀ (endpointCoordinates G q₀ (V, z.2), z.2)
          (fderiv ℝ (endpointCoordinates G q₀) (V, z.2) (0, 1)) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  obtain ⟨hτ, hmax, _, _⟩ := hreg.1
  have hsrc : z ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have hregn : ∀ᶠ V in 𝓝 z.1, (V, z.2) ∈ G.toLExponentialFamily.regularDomain := by
    have h := (continuousAt_id.prodMk continuousAt_const)
      (G.regular_chart.open_source.mem_nhds hsrc)
    simpa only [G.regular_source, Filter.mem_map, mem_preimage, id_eq] using! h
  have hγ := G.gamma_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ z.1, hτ, hmax⟩)
  have hc : ContinuousAt (fun V ↦ G.gamma V z.2) z.1 :=
    hγ.continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  filter_upwards [hregn, hc ((chartAt (EuclideanSpace ℝ (Fin n)) q₀).open_source.mem_nhds hq)]
    with V hV hqV
  exact coordinate_terminal_pairing hL G q₀ (V, z.2) hV hqV v

set_option backward.isDefEq.respectTransparency false in

theorem endpoint_gram_diagonal_hasDerivAt
    (hwindow : Icc (T - τmax) T ⊆ J) (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (z : TangentSpace (𝓡 n) p × ℝ)
    (hreg : z ∈ G.toLExponentialFamily.regularDomain) (h : TangentSpace (𝓡 n) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    let q := G.gamma z.1 z.2
    let E := endpointCoordinates G q
    let B := coordinateBackwardMetric F T q
    let v : TangentSpace (𝓡 n) q := fderiv ℝ E z (h, 0)
    HasDerivAt (fun t ↦ B (E (z.1, t), t)
        (fderiv ℝ E (z.1, t) (h, 0)) (fderiv ℝ E (z.1, t) (h, 0)))
      (2 * (F.connection (T - z.2)).ricci q v v +
        2 * (F.connection (T - z.2)).hessian (fun x ↦ reducedLength F T p x z.2) q v v)
      z.2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let q := G.gamma z.1 z.2
  let E := endpointCoordinates G q
  let B := coordinateBackwardMetric F T q
  let v : EuclideanSpace ℝ (Fin n) := fderiv ℝ E z (h, 0)
  let w : EuclideanSpace ℝ (Fin n) := fderiv ℝ E z (0, 1)
  let k : EuclideanSpace ℝ (Fin n) := fderiv ℝ (fderiv ℝ E) z (0, 1) (h, 0)
  let f := fun x ↦ reducedLength F T p x z.2
  let l := f ∘ (extChartAt (𝓡 n) q).symm
  obtain ⟨hτ, hmax, hmin, _⟩ := hreg.1
  have hz : z ∈ univ ×ˢ Ioo 0 τmax := ⟨mem_univ _, hτ, hmax⟩
  have hq : G.gamma z.1 z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source :=
    mem_chart_source _ _
  have hE : ContDiffAt ℝ 2 E z := (endpointCoordinates_contDiffAt G q z hz hq).of_le (by decide)
  have hB : DifferentiableAt ℝ B (E z, z.2) :=
    (coordinateBackwardMetric_contDiffAt hwindow q hτ hmax).differentiableAt (by simp)
  have hsrc : z ∈ G.regular_chart.source := G.regular_source.symm ▸ hreg
  have htgt : (q, z.2) ∈ G.regular_chart.target := by
    simpa only [G.regular_forward, q] using G.regular_chart.map_source hsrc
  have hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q :=
    (reducedLength_space_contMDiffAt (G.regular_point (q, z.2) htgt)).of_le (by decide)
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) 2 (extChartAt (𝓡 n) q).symm (E z) :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt (extChartAt_target_mem_nhds (I := 𝓡 n) q)
  have hl : ContDiffAt ℝ 2 l (E z) := by
    have hf' : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f ((extChartAt (𝓡 n) q).symm (E z)) := by
      change ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f
        ((extChartAt (𝓡 n) q).symm (extChartAt (𝓡 n) q q))
      simpa only [extChartAt_to_inv] using hf
    exact (hf'.comp (E z) hi).contDiffAt
  have hw : w = curveVelocity (G.gamma z.1) z.2 := by
    dsimp only [w, E]
    rw [endpointCoordinates_time G q z hz hq,
      TangentBundle.continuousLinearMapAt_trivializationAt hq, mfderiv_extChartAt_self]
    rfl
  have hdual (a : TangentSpace (𝓡 n) q) : mvfderiv (𝓡 n) f q a =
      (F.metric (T - z.2)).inner q w a := by
    rw [hw]
    exact reducedLength_differential_eq_terminal_pairing hL G z.1 hτ hmax hmin
      (hf.mdifferentiableAt two_ne_zero) hreg.2.2 a
  have hmix := terminal_pairing_second_derivative hE hB hl h v
    (coordinate_terminal_pairing_eventually hL G q z hreg hq v)
  have hhess := preferred_hessian_of_metric_dual (F.metric (T - z.2))
    (F.connection (T - z.2)) q hf v w hdual
  have htime := coordinateBackwardMetric_time_derivative (F := F) hwindow hτ hmax q v v
  have hspace₁ := coordinateBackwardMetric_space_derivative (F := F) hwindow hτ hmax q v w v
  have hspace₂ := coordinateBackwardMetric_space_derivative (F := F) hwindow hτ hmax q w v v
  have hsym : (fun x ↦ (F.metric (T - z.2)).inner x
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q) w x)
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q) v x)) =
      (fun x ↦ (F.metric (T - z.2)).inner x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (E := TangentSpace (𝓡 n)) (x := q) v x)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (E := TangentSpace (𝓡 n)) (x := q) w x)) := by
    funext x
    exact (F.metric (T - z.2)).symm x _ _
  rw [hsym] at hspace₁
  have hgram := endpoint_gram_hasDerivAt hE hB h h
  convert hgram using 1
  change 2 * (F.connection (T - z.2)).ricci q v v +
      2 * (F.connection (T - z.2)).hessian f q v v =
    fderiv ℝ B (E z, z.2) (w, 1) v v + B (E z, z.2) k v + B (E z, z.2) v k
  have hsplit : (w, (1 : ℝ)) = (w, 0) + (0, 1) := by simp
  rw [hsplit, map_add, add_apply, add_apply]
  change fderiv ℝ (fderiv ℝ l) (E z) v v =
    fderiv ℝ B (E z, z.2) (v, 0) w v + B (E z, z.2) k v at hmix
  change fderiv ℝ B (E z, z.2) (0, 1) v v = _ at htime
  change fderiv ℝ B (E z, z.2) (v, 0) w v = _ at hspace₁
  change fderiv ℝ B (E z, z.2) (w, 0) v v = _ at hspace₂
  have hcenter (a b : EuclideanSpace ℝ (Fin n)) :
      B (E z, z.2) a b = (F.metric (T - z.2)).inner q a b :=
    coordinateBackwardMetric_at_center q z.2 a b
  have hcsym : B (E z, z.2) v k = B (E z, z.2) k v :=
    (hcenter v k).trans (((F.metric (T - z.2)).symm q v k).trans (hcenter k v).symm)
  have hhess' : (F.connection (T - z.2)).hessian f q v v =
      fderiv ℝ (fderiv ℝ l) (E z) v v -
        fderiv ℝ B (E z, z.2) (v, 0) w v + fderiv ℝ B (E z, z.2) (w, 0) v v / 2 := by
    rw [hspace₁, hspace₂]
    exact hhess
  rw [hcsym]
  linarith only [hmix, htime, hhess']

end PoincareConjecture.M10
