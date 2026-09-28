import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem GeneralizedRicciFlowData.box_scalar (F : GeneralizedRicciFlowData.{u})
    (b : F.box_index) (t : ℝ) (ht : t ∈ (F.box b).interval)
    (x : (F.box b).carrier.carrier) :
    ((F.box b).flow.connection t).scalarCurvature x =
      (F.connection t).scalarCurvature ((F.box b).forward t ht x) := by
  exact ((F.box b).flow.connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ ((F.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => ((F.box b).metric_pullback t ht y v w).symm) (mem_univ x)

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


theorem exists_regular_collar (H : SingularTimeAssumptions F T M) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, t ∉ H.singularTimes := by
  obtain ⟨delta, hdelta, hsep⟩ := H.singularTimes_discrete T H.terminal_is_singular
  let s := (max H.reference.tMinus (T - delta) + T) / 2
  have hmax : max H.reference.tMinus (T - delta) < T :=
    max_lt H.reference.tMinus_lt (sub_lt_self T hdelta)
  have hsref : H.reference.tMinus < s := by
    dsimp [s]
    linarith [le_max_left H.reference.tMinus (T - delta)]
  have hsdelta : T - delta < s := by
    dsimp [s]
    linarith [le_max_right H.reference.tMinus (T - delta)]
  have hsT : s < T := by dsimp [s]; linarith
  refine ⟨s, hsref, hsT, ?_⟩
  intro t ht hsingular
  have hdist := hsep t hsingular ht.2.ne
  rw [abs_of_neg (sub_neg.mpr ht.2)] at hdist
  linarith [ht.1]


theorem compact_reference (H : SingularTimeAssumptions F T M) : CompactSpace M := by
  obtain ⟨s, hsref, hsT, hregular⟩ := H.exists_regular_collar
  have hs : s ∈ Ico H.reference.tMinus T := ⟨hsref.le, hsT⟩
  have hcompact := H.regular_slices_compact s (H.reference.window_subset hs)
    (hregular s ⟨le_rfl, hsT⟩)
  apply isCompact_univ_iff.mp
  have himage : H.reference.inverse s hs '' (univ : Set (F.slice s).carrier) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact ⟨H.reference.forward s hs x, mem_univ _, H.reference.left_inverse s hs x⟩
  rw [← himage]
  exact hcompact.image (H.reference.inverse_smooth s hs).continuous


theorem reference_scalar_continuousOn (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (x : M) :
    ContinuousOn (fun t => H.reference.scalar t x) (Ico H.reference.tMinus T) := by
  have hj : ContinuousOn (fun p : ℝ × M =>
      (H.reference.flow.connection p.1).scalarCurvature p.2)
      (Ico H.reference.tMinus T ×ˢ univ) :=
    (P04.scalar_regular 3 M _ H.reference.flow).continuousOn
  exact hj.comp (f := fun t : ℝ => (t, x))
    (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, mem_univ x⟩)


theorem reference_scalar_continuous (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T) :
    Continuous (H.reference.scalar t) := by
  have hj : ContinuousOn (fun p : ℝ × M =>
      (H.reference.flow.connection p.1).scalarCurvature p.2)
      (Ico H.reference.tMinus T ×ˢ univ) :=
    (P04.scalar_regular 3 M _ H.reference.flow).continuousOn
  exact hj.comp_continuous (f := fun x : M => (t, x))
    (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)


theorem reference_scalar_derivative_bound (H : SingularTimeAssumptions F T M)
    (x : M) (t : ℝ) (ht : t ∈ Ioo H.reference.tMinus T)
    (hR : H.r₀⁻¹ ^ 2 ≤ H.reference.scalar t x) :
    ∃ d : ℝ, HasDerivAt (fun s => H.reference.scalar s x) d t ∧
      |d| ≤ H.analytic_constant * H.reference.scalar t x ^ 2 := by
  have ht' : t ∈ Ico H.reference.tMinus T := ⟨ht.1.le, ht.2⟩
  obtain ⟨b, y, delta, hdelta, hbox⟩ := H.reference.vertical_compatibility t ht' x
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo H.reference.tMinus T ∧ |s - t| < delta := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2, Metric.ball_mem_nhds t hdelta] with s hs hdist
    exact ⟨hs, by simpa only [Metric.mem_ball, Real.dist_eq] using hdist⟩
  have hmem : (F.box b).interval ∈ 𝓝 t := by
    filter_upwards [hnear] with s hs
    exact (hbox s ⟨hs.1.1.le, hs.1.2⟩ hs.2).choose
  have heq : (fun s => H.reference.scalar s x) =ᶠ[𝓝 t]
      (fun s => ((F.box b).flow.connection s).scalarCurvature y) := by
    filter_upwards [hnear] with s hs
    obtain ⟨hb, hforward⟩ := hbox s ⟨hs.1.1.le, hs.1.2⟩ hs.2
    dsimp only [SingularTimeReference.scalar]
    rw [← H.reference.scalar_pullback s ⟨hs.1.1.le, hs.1.2⟩ x,
      hforward, ← F.box_scalar b s hb y]
  have heqt := heq.eq_of_nhds
  obtain ⟨d, hd, hbound⟩ := H.scalar_time_derivative_bound b t (mem_of_mem_nhds hmem) y
    (by simpa only [← heqt] using hR)
  refine ⟨d, (hd.hasDerivAt hmem).congr_of_eventuallyEq heq, ?_⟩
  simpa only [← heqt] using hbound


theorem reference_scalar_lower_bound (H : SingularTimeAssumptions F T M) :
    ∃ L : ℝ, ∀ t ∈ Ico H.reference.tMinus T, ∀ x : M, L ≤ H.reference.scalar t x := by
  obtain ⟨L, hL⟩ := H.curvature_lower_bound
  refine ⟨L, fun t ht x => ?_⟩
  dsimp only [SingularTimeReference.scalar]
  rw [← H.reference.scalar_pullback t ht x]
  exact hL ⟨t, H.reference.forward t ht x⟩ (H.reference.window_subset ht)

end SingularTimeAssumptions
end PoincareConjecture
