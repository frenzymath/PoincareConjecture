import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Continuation.Compact








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open PoincareConjecture.ReducedLengthMinimum.Variational
open PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance orthDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance orthDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance orthBilinGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance orthBilinSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem IsAdaptedFieldOn.pairing_hasDerivAt {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M)
    (P Q : ∀ s, TangentSpace (𝓡 n) (γ s)) (U : Set ℝ) (hU : IsOpen U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    {s : ℝ} (hs : s ∈ U) :
    HasDerivAt (fun r ↦ (F.metric (T - r ^ 2)).inner (γ r) (P r) (Q r)) 0 s := by
  let x := γ s
  let V := U ∩ γ ⁻¹' (chartAt E x).source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E x).open_source
  have hsV : s ∈ V := ⟨hs, mem_chart_source E x⟩
  let y : ℝ → E := fun r ↦ extChartAt (𝓡 n) x (γ r)
  have hy : ContDiffOn ℝ ∞ y V := by
    apply ContMDiffOn.contDiffOn
    exact (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp
      (hγ.mono inter_subset_left) (fun r hr ↦ by
        simpa only [extChartAt_source, mem_preimage] using hr.2)
  let v := fieldChartCoordinates x γ P
  let w := fieldChartCoordinates x γ Q
  have hz : (s, y s) ∈ chartActionDomain F T x :=
    ⟨htime s hs, (extChartAt (𝓡 n) x).map_source (by
      simpa only [extChartAt_source, mem_preimage] using hsV.2)⟩
  let G := chartActionMetric F T x
  have hG : DifferentiableAt ℝ G (s, y s) :=
    (((chartActionMetric_contDiffOn F T x) _ hz).contDiffAt
      ((chartActionDomain_open F T x).mem_nhds hz)).differentiableAt (by simp)
  have hyr := ((hy s hsV).contDiffAt (hV.mem_nhds hsV)).differentiableAt (by simp)
  have hc := hG.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk hyr.hasDerivAt)
  have hdv := hP.equation s hs x hsV.2
  have hdw := hQ.equation s hs x hsV.2
  have hp := (hc.clm_apply hdv).clm_apply hdw
  have hsym : ∀ᶠ z in 𝓝 (s, y s), ∀ v w, G z v w = G z w v := by
    filter_upwards [(chartActionDomain_open F T x).mem_nhds hz] with z hz'
    exact chartActionMetric_symm F T x hz'
  have hzero := chartTransportOperator_metric_identity G (s, y s) hG hsym
    (chartActionMetric_pos F T x hz) (deriv y s) (v s) (w s)
  have hp' : HasDerivAt (fun r ↦ G (r, y r) (v r) (w r)) 0 s := by
    apply hp.congr_deriv
    simpa only [Function.comp_def, id_eq, add_apply] using hzero
  apply hp'.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hsV] with r hr
  symm
  change chartActionMetric F T x (r, extChartAt (𝓡 n) x (γ r))
    (fieldChartCoordinates x γ P r) (fieldChartCoordinates x γ Q r) = _
  rw [chartActionMetric_apply F T hr.2,
    chartFrame_fieldChartCoordinates x γ P hr.2, chartFrame_fieldChartCoordinates x γ Q hr.2]

theorem IsAdaptedFieldOn.pairing_eq {J : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) (γ : ℝ → M)
    (P Q : ∀ s, TangentSpace (𝓡 n) (γ s)) (U : Set ℝ) (hU : IsOpen U)
    (hconn : IsPreconnected U)
    (htime : ∀ s ∈ U, s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    (s t : ℝ) (hs : s ∈ U) (ht : t ∈ U) :
    (F.metric (T - s ^ 2)).inner (γ s) (P s) (Q s) =
      (F.metric (T - t ^ 2)).inner (γ t) (P t) (Q t) := by
  have hd (r : ℝ) (hr : r ∈ U) :=
    IsAdaptedFieldOn.pairing_hasDerivAt F T γ P Q U hU htime hγ hP hQ hr
  exact hU.is_const_of_deriv_eq_zero
    (f := fun r ↦ (F.metric (T - r ^ 2)).inner (γ r) (P r) (Q r)) hconn
    (fun r hr ↦ (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr ↦ (hd r hr).deriv) hs ht

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem exists_smooth_adapted_orthonormal_frame_surface
    (F : RicciFlow 2 M (Iic 0)) (γ : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ U)
    (c : ℝ) (hc : 0 ≤ c) (hCU : Icc 0 c ⊆ U) :
    ∃ (D : Set ℝ) (P : Fin 2 → ∀ s, TangentSpace (𝓡 2) (γ s)),
      IsOpen D ∧ IsPreconnected D ∧ Icc 0 c ⊆ D ∧ D ⊆ U ∧
        (∀ i, IsAdaptedFieldOn F 0 γ (P i) D) ∧
        ∀ s ∈ D, ∀ i j, (F.metric (0 - s ^ 2)).inner (γ s) (P i s) (P j s) =
          if i = j then 1 else 0 := by
  classical
  let g := F.metric (0 - (0 : ℝ) ^ 2)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) (γ 0)) = 2 := finrank_euclideanSpace_fin
  let e : Fin 2 → TangentSpace (𝓡 2) (γ 0) :=
    fun i ↦ g.orthonormalBasis (γ 0) (Fin.cast hdim.symm i)
  have he (i j : Fin 2) : g.inner (γ 0) (e i) (e j) = if i = j then 1 else 0 := by
    change inner ℝ (g.orthonormalBasis (γ 0) (Fin.cast hdim.symm i))
      (g.orthonormalBasis (γ 0) (Fin.cast hdim.symm j)) = _
    simpa using (g.orthonormalBasis (γ 0)).inner_eq_ite
      (Fin.cast hdim.symm i) (Fin.cast hdim.symm j)
  choose D P hD hconn hCD hDU hP₀ hP using fun i : Fin 2 ↦
    exists_adaptedFieldOn_Icc F 0 γ U hU (fun s _ ↦ ancient_squareTime_mem_interior s)
      hγ 0 c 0 hCU ⟨le_rfl, hc⟩ (e i)
  let W := ⋂ i : Fin 2, D i
  have hW : IsOpen W := isOpen_iInter_of_finite hD
  have hconnW : IsPreconnected W :=
    (Set.ordConnected_iInter fun i ↦ (hconn i).ordConnected).isPreconnected
  have hCW : Icc 0 c ⊆ W := fun s hs ↦ mem_iInter.mpr (fun i ↦ hCD i hs)
  have hWi (i : Fin 2) : W ⊆ D i := fun _ hs ↦ mem_iInter.mp hs i
  have hWU : W ⊆ U := (hWi 0).trans (hDU 0)
  have hPW (i : Fin 2) := (hP i).mono (hWi i)
  refine ⟨W, P, hW, hconnW, hCW, hWU, hPW, ?_⟩
  intro s hs i j
  have hp := IsAdaptedFieldOn.pairing_eq F 0 γ (P i) (P j) W hW hconnW
    (fun r _ ↦ ancient_squareTime_mem_interior r) (hγ.mono hWU)
    (hPW i) (hPW j) s 0 hs (hCW ⟨le_rfl, hc⟩)
  rw [hp, hP₀ i, hP₀ j]
  exact he i j

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
