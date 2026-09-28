import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Extension.Pinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.Sectional.Rayleigh
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.DeepHorn

open RicciFlowAnalysis

section Sectional

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 X}

private theorem sectional_changeBasis (D : LeviCivitaData g) (x : X)
    (u v : TangentSpace (𝓡 3) x) (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) :
    D.sectionalCurvature x (a • u + b • v) (c • u + d • v) =
      D.sectionalCurvature x u v := by
  have hnum : D.curvatureTensor x (a • u + b • v) (c • u + d • v)
      (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
    simp only [D.curvatureTensor_add_first, D.curvatureTensor_add_second,
      D.curvatureTensor_add_third, D.curvatureTensor_add_last,
      D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
      D.curvatureTensor_smul_third, D.curvatureTensor_smul_last,
      D.curvatureTensor_zero_first, D.curvatureTensor_zero_last]
    simp only [D.curvatureTensor_swap_first x v u,
      D.curvatureTensor_swap_last x u v v u]
    ring
  have hgram : metricGram g x (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * metricGram g x u v := by
    simp only [metricGram, map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      g.symm x v u]
    ring
  change _ / metricGram g x _ _ = _ / metricGram g x _ _
  rw [hnum, hgram]
  field_simp [hdet]

private theorem orthonormalPair_linearIndependent (x : X)
    (u v : TangentSpace (𝓡 3) x) (huv : LeviCivitaData.IsOrthonormalPair g x u v) :
    LinearIndependent ℝ ![u, v] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnormu : ‖u‖ = 1 := by
    have hu : inner ℝ u u = 1 := huv.1
    nlinarith [real_inner_self_eq_norm_sq u, norm_nonneg u]
  have hnormv : ‖v‖ = 1 := by
    have hv : inner ℝ v v = 1 := huv.2.1
    nlinarith [real_inner_self_eq_norm_sq v, norm_nonneg v]
  have horth : Orthonormal ℝ (![u, v] : Fin 2 → TangentSpace (𝓡 3) x) := by
    constructor
    · intro i
      fin_cases i
      · exact hnormu
      · exact hnormv
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact huv.2.2
      · change inner ℝ v u = 0
        rw [real_inner_comm]
        exact huv.2.2
      · exact (hij rfl).elim
  exact horth.linearIndependent

private theorem sectional_values_eq_model_image (D : LeviCivitaData g) (x : X)
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] TangentSpace (𝓡 3) x) :
    {k : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v ∧ k = D.curvatureTensor x u v u v} =
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        D.sectionalCurvature x (e p.1) (e p.2)) '' modelOrthonormalPairs 3 := by
  ext k
  constructor
  · rintro ⟨u, v, huv, hk⟩
    have hlin := (orthonormalPair_linearIndependent x u v huv).map'
      e.symm.toLinearMap (LinearMap.ker_eq_bot.mpr e.symm.injective)
    have hlin' : LinearIndependent ℝ ![e.symm u, e.symm v] := by
      convert! hlin using 1
      ext i
      fin_cases i <;> rfl
    obtain ⟨a, b, c, d, hdet, hp, hq, hpq⟩ :=
      LeviCivitaData.exists_orthonormal_changeBasis (e.symm u) (e.symm v) hlin'
    refine ⟨(a • e.symm u + b • e.symm v, c • e.symm u + d • e.symm v), ?_, ?_⟩
    · refine ⟨?_, ?_, hpq⟩
      · nlinarith [real_inner_self_eq_norm_sq (a • e.symm u + b • e.symm v),
          norm_nonneg (a • e.symm u + b • e.symm v)]
      · nlinarith [real_inner_self_eq_norm_sq (c • e.symm u + d • e.symm v),
          norm_nonneg (c • e.symm u + d • e.symm v)]
    · simp only [map_add, map_smul, e.apply_symm_apply]
      rw [sectional_changeBasis D x u v a b c d hdet]
      simp only [LeviCivitaData.sectionalCurvature, huv.1, huv.2.1, huv.2.2,
        one_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, div_one]
      exact hk.symm
  · rintro ⟨⟨p, q⟩, hpq, hk⟩
    have horth : Orthonormal ℝ (![p, q] : Fin 2 → EuclideanSpace ℝ (Fin 3)) := by
      constructor
      · intro i
        fin_cases i
        · exact hpq.1
        · exact hpq.2.1
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hpq.2.2
        · change inner ℝ q p = 0
          rw [real_inner_comm]
          exact hpq.2.2
        · exact (hij rfl).elim
    have hlin := horth.linearIndependent.map' e.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.injective)
    have hlin' : LinearIndependent ℝ ![e p, e q] := by
      convert! hlin using 1
      ext i
      fin_cases i <;> rfl
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
      ⟨g.toRiemannianMetric⟩
    obtain ⟨a, b, c, d, hdet, hu, hv, huv⟩ :=
      LeviCivitaData.exists_orthonormal_changeBasis (e p) (e q) hlin'
    refine ⟨a • e p + b • e q, c • e p + d • e q, ⟨hu, hv, huv⟩, ?_⟩
    change D.sectionalCurvature x (e p) (e q) = k at hk
    rw [← hk, ← sectional_changeBasis D x (e p) (e q) a b c d hdet]
    change _ / (inner ℝ (a • e p + b • e q) (a • e p + b • e q) *
      inner ℝ (c • e p + d • e q) (c • e p + d • e q) -
      (inner ℝ (a • e p + b • e q) (c • e p + d • e q)) ^ 2) = _
    rw [hu, hv, huv]
    norm_num

theorem flow_leastSectionalCurvature_continuousOn {J : Set ℝ}
    (G : RicciFlow 3 X J) (x : X) :
    ContinuousOn (fun t => (G.connection t).leastSectionalCurvature x) J := by
  let V := EuclideanSpace ℝ (Fin 3)
  let e := trivializationAt V (TangentSpace (𝓡 3) : X → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let L : V ≃ₗ[ℝ] TangentSpace (𝓡 3) x :=
    (e.continuousLinearEquivAt ℝ x hx).symm.toLinearEquiv
  have hL (v : V) : L v = e.symmL ℝ x v := by
    exact congrFun (e.symm_continuousLinearEquivAt_eq hx) v
  let P := modelOrthonormalPairs 3
  let : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_modelOrthonormalPairs 3)
  let f (t : J) (p : P) : ℝ :=
    (G.connection t).sectionalCurvature x (e.symmL ℝ x p.1.1) (e.symmL ℝ x p.1.2)
  have hf : Continuous (Function.uncurry f) := by
    have h := (continuousOn_flow_sectionalRayleigh_trivialization G x).comp_continuous
      (((continuous_subtype_val.comp continuous_fst).prodMk continuous_const).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun p : J × P => ⟨⟨p.1.property, hx⟩, p.2.property⟩)
    exact h
  have himage (t : J) : f t '' univ =
      (fun p : V × V => (G.connection t).sectionalCurvature x (L p.1) (L p.2)) '' P := by
    ext k
    constructor
    · rintro ⟨p, _, hp⟩
      exact ⟨p.1, p.2, by simpa only [f, hL] using hp⟩
    · rintro ⟨p, hp, hk⟩
      exact ⟨⟨p, hp⟩, mem_univ _, by simpa only [f, hL] using hk⟩
  have hmin := (isCompact_univ : IsCompact (univ : Set P)).continuous_sInf (f := f) hf
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hmin.congr
  intro t
  rw [himage]
  exact congrArg sInf (sectional_values_eq_model_image (G.connection t) x L).symm

theorem flow_negativeCurvaturePart_continuousOn {J : Set ℝ}
    (G : RicciFlow 3 X J) (x : X) :
    ContinuousOn (fun t => (G.connection t).negativeCurvaturePart x) J :=
  (flow_leastSectionalCurvature_continuousOn G x).neg.sup continuousOn_const

end Sectional

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]

private theorem terminal_box_eventually
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hT : T ∈ (E.extended.box b).interval) :
    ∀ᶠ t in 𝓝[<] T, t ∈ F.interval ∧ t ∈ (E.extended.box b).interval := by
  have hpos : 0 < T := lt_of_le_of_lt
    (H.interval_nonnegative H.reference.tMinus_mem) H.reference.tMinus_lt
  obtain ⟨U, hU, heq⟩ := (E.extended.box b).relatively_open
  have hTU : T ∈ U := (heq ▸ hT).2
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds hpos),
    nhdsWithin_le_nhds (hU.mem_nhds hTU)] with t ht ht0 htU
  have htF : t ∈ F.interval := H.interval_exhausts_preterminal ⟨ht0.le, ht⟩
  exact ⟨htF, heq ▸ ⟨E.old_times htF, htU⟩⟩

private theorem box_scalar_pullback (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval)
    (x : (G.box b).carrier.carrier) :
    (G.connection t).scalarCurvature ((G.box b).forward t ht x) =
      ((G.box b).flow.connection t).scalarCurvature x := by
  exact (((G.box b).flow.connection t).scalarCurvature_eq_of_local_isometry
    (G.connection t) isOpen_univ ((G.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => ((G.box b).metric_pullback t ht y v w).symm) (mem_univ x)).symm

private theorem box_negativeCurvaturePart_pullback (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval)
    (x : (G.box b).carrier.carrier) :
    (G.connection t).negativeCurvaturePart ((G.box b).forward t ht x) =
      ((G.box b).flow.connection t).negativeCurvaturePart x := by
  exact (((G.box b).flow.connection t).negativeCurvaturePart_eq_of_local_isometry
    (G.connection t) isOpen_univ ((G.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => ((G.box b).metric_pullback t ht y v w).symm) (mem_univ x)).symm

theorem terminal_box_hamiltonIvey_pinching
    (hM04 : RicciFlowCurvatureCalculus.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hT : T ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier) :
    -6 / (1 + 4 * T) ≤ ((E.extended.box b).flow.connection T).scalarCurvature x ∧
      (0 < ((E.extended.box b).flow.connection T).negativeCurvaturePart x →
        2 * ((E.extended.box b).flow.connection T).negativeCurvaturePart x *
          (Real.log (((E.extended.box b).flow.connection T).negativeCurvaturePart x) +
            Real.log (1 + T) - 3) ≤
          ((E.extended.box b).flow.connection T).scalarCurvature x) := by
  have hpos : 0 < T := lt_of_le_of_lt
    (H.interval_nonnegative H.reference.tMinus_mem) H.reference.tMinus_lt
  have hevent := terminal_box_eventually H E b hT
  have hfilter : 𝓝[<] T ≤ 𝓝[(E.extended.box b).interval] T :=
    nhdsWithin_le_iff.mpr (hevent.mono fun _ ht => ht.2)
  have hscalar := (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
    ricciFlowCurvatureTheory _ (E.extended.box b).flow x T hT).tendsto.mono_left hfilter
  have hnegative := (flow_negativeCurvaturePart_continuousOn (E.extended.box b).flow x T hT).tendsto.mono_left hfilter
  have htime : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · have hbarrier : Tendsto (fun t : ℝ => -6 / (1 + 4 * t)) (𝓝[<] T)
        (𝓝 (-6 / (1 + 4 * T))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add (htime.const_mul 4)) (by linarith)
    apply le_of_tendsto_of_tendsto hbarrier hscalar
    filter_upwards [hevent] with t ht
    have h := (extension_hamiltonIveyPinchedAt_old H E t ht.1).2.2.1
      ((E.extended.box b).forward t ht.2 x)
    simpa only [GeneralizedRicciFlowData.scalar, box_scalar_pullback] using h
  · intro hn
    have hlogtime : Tendsto (fun t : ℝ => Real.log (1 + t)) (𝓝[<] T)
        (𝓝 (Real.log (1 + T))) :=
      (tendsto_const_nhds.add htime).log (by linarith)
    have hmodel := (hnegative.const_mul 2).mul
      (((hnegative.log hn.ne').add hlogtime).sub (tendsto_const_nhds (x := (3 : ℝ))))
    apply le_of_tendsto_of_tendsto hmodel hscalar
    filter_upwards [hevent, hnegative.eventually (Ioi_mem_nhds hn)] with t ht hnt
    have h := (extension_hamiltonIveyPinchedAt_old H E t ht.1).2.2.2
      ((E.extended.box b).forward t ht.2 x)
    simp only [GeneralizedRicciFlowData.scalar, box_scalar_pullback,
      box_negativeCurvaturePart_pullback] at h
    exact h hnt

theorem extension_hamiltonIveyPinchedAt_terminal
    (hM04 : RicciFlowCurvatureCalculus.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (hT : T ∈ E.extended.interval) : generalizedHamiltonIveyPinchedAt E.extended T := by
  have hpos : 0 < T := lt_of_le_of_lt
    (H.interval_nonnegative H.reference.tMinus_mem) H.reference.tMinus_lt
  refine ⟨hT, hpos.le, ?_, ?_⟩
  · intro x
    obtain ⟨b, hb, y, rfl⟩ := E.extended.box_covers T x
    change -6 / (1 + 4 * T) ≤ (E.extended.connection T).scalarCurvature _
    rw [box_scalar_pullback]
    exact (terminal_box_hamiltonIvey_pinching hM04 H E b hb y).1
  · intro x
    obtain ⟨b, hb, y, rfl⟩ := E.extended.box_covers T x
    change 0 < (E.extended.connection T).negativeCurvaturePart _ → _
    rw [box_negativeCurvaturePart_pullback]
    change 0 < ((E.extended.box b).flow.connection T).negativeCurvaturePart y →
      _ ≤ (E.extended.connection T).scalarCurvature _
    rw [box_scalar_pullback]
    exact (terminal_box_hamiltonIvey_pinching hM04 H E b hb y).2

theorem extension_hamiltonIveyPinched
    (hM04 : RicciFlowCurvatureCalculus.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T) :
    generalizedHamiltonIveyPinched E.extended := by
  intro t ht
  rcases E.times_subset ht with htold | htT
  · exact extension_hamiltonIveyPinchedAt_old H E t htold
  · have htT' : t = T := mem_singleton_iff.mp htT
    subst t
    exact extension_hamiltonIveyPinchedAt_terminal hM04 H E ht

end PoincareConjecture.DeepHorn
