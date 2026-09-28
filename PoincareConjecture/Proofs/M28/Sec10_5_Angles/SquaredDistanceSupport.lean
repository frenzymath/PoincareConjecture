import PoincareConjecture.Proofs.M28.Sec10_5_Angles.AffineParallelField
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.MovingEndpointEnergy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Uniqueness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Neighborhood
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.NoBranching

open Set Filter
open scoped Topology ContDiff Manifold Bundle

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.M28.Comparison

open RiemannianMetric Conjugate.Realization

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in
private theorem geodesic_open_buffer
    {g : RiemannianMetric n M} {γ : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (hγ : g.IsGeodesicOn γ (Icc a b)) :
    ∃ e > 0, g.IsGeodesicOn γ (Ioo (a - e) (b + e)) := by
  let O : Set ℝ := {t | ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ g.IsGeodesicOn γ U}
  have hO : IsOpen O := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro t ⟨U, hU, htU, hgeoU⟩
    exact mem_of_superset (hU.mem_nhds htU) (fun s hs => ⟨U, hU, hs, hgeoU⟩)
  have hsub : Icc a b ⊆ O := by
    intro t ht
    exact hγ.exists_open_nhds ht
  have hgeoO : g.IsGeodesicOn γ O := by
    rintro t ⟨U, _, htU, hgeoU⟩
    exact hgeoU t htU
  obtain ⟨e, he, hbuffer⟩ := exists_Icc_enlarged_subset hO hab hsub
  exact ⟨e, he, fun t ht => hgeoO t (hbuffer (Ioo_subset_Icc_self ht))⟩

omit [T2Space M] in
private theorem hasDerivAt_center_chart_of_geodesic
    {g : RiemannianMetric n M} {γ : ℝ → M} {S : Set ℝ}
    (hγ : g.IsGeodesicOn γ S) {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun u => extChartAt (𝓡 n) (γ t) (γ u))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) t := by
  have hd := (hγ.hasDerivAt_chart_at ht (γ t) (mem_extChartAt_source _)).1
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (γ t)) (γ t) :=
    mdifferentiableAt_extChartAt (mem_chart_source _ _)
  have hchain := mfderiv_comp t hc
    ((hγ.contMDiffAt ht).mdifferentiableAt one_ne_zero)
  rw [mfderiv_eq_fderiv] at hchain
  have hv := congrArg (fun A => A (1 : ℝ)) hchain
  change deriv (fun u => extChartAt (𝓡 n) (γ t) (γ u)) t =
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (γ t)) (γ t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) at hv
  rw [mfderiv_extChartAt_self] at hv
  change deriv (fun u => extChartAt (𝓡 n) (γ t) (γ u)) t =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 at hv
  exact hd.congr_deriv hv

omit [T2Space M] in
private theorem squared_distance_support_at_base_point
    (g : RiemannianMetric n M) {β : ℝ → M} {δ : ℝ}
    (hδ : 0 < δ) (hβ : g.IsGeodesicOn β (Ioo (-δ) δ)) :
    ∃ H : ℝ → ℝ, ContDiffAt ℝ 2 H 0 ∧ H 0 = 0 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), g.edist (β 0) (β s) ≠ ⊤ ∧
        (g.edist (β 0) (β s)).toReal ^ 2 ≤ H s) ∧
      deriv (deriv H) 0 ≤ 2 * g.inner (β 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β 0 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β 0 1) := by
  let w := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β 0 1
  let c := g.tangentNorm (β 0) w
  let H : ℝ → ℝ := fun s => c ^ 2 * s ^ 2
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = g.inner (β 0) w w := by
    apply Real.sq_sqrt
    by_cases hw : w = 0
    · simp [hw]
    · exact (g.pos (β 0) w hw).le
  have hβcc : g.IsGeodesicOn β (Icc (-δ / 2) (δ / 2)) := by
    intro t ht
    exact hβ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0 : (0 : ℝ) ∈ Icc (-δ / 2) (δ / 2) := ⟨by linarith, by linarith⟩
  have hspeed (t : ℝ) (ht : t ∈ Icc (-δ / 2) (δ / 2)) :
      g.tangentNorm (β t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β t 1) = c :=
    Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hβcc ht h0
  have hnear : Ioo (-δ / 2) (δ / 2) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hmajor : ∀ᶠ s in 𝓝 (0 : ℝ), g.edist (β 0) (β s) ≠ ⊤ ∧
      (g.edist (β 0) (β s)).toReal ^ 2 ≤ H s := by
    filter_upwards [hnear] with s hs
    have hb : g.edist (β 0) (β s) ≤ ENNReal.ofReal (|s| * c) := by
      simpa only [zero_sub, abs_neg] using
        Poincare.VolumeComparison.edist_le_of_geodesic_speed_Icc g hβcc hspeed
          h0 (Ioo_subset_Icc_self hs)
    have hfinite : g.edist (β 0) (β s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
    have hnonneg : 0 ≤ |s| * c := mul_nonneg (abs_nonneg s) hc
    have hreal : (g.edist (β 0) (β s)).toReal ≤ |s| * c := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      simpa only [ENNReal.toReal_ofReal hnonneg] using hh
    refine ⟨hfinite, ?_⟩
    have hsquare := mul_le_mul hreal hreal ENNReal.toReal_nonneg hnonneg
    rw [← pow_two, ← pow_two, mul_pow, sq_abs] at hsquare
    simpa only [H, mul_comm] using hsquare
  have hH2 : ContDiffAt ℝ 2 H 0 := contDiffAt_const.mul (contDiffAt_id.pow 2)
  have hD (s : ℝ) : HasDerivAt H (2 * c ^ 2 * s) s := by
    have hd := ((hasDerivAt_id s).pow 2).const_mul (c ^ 2)
    exact hd.congr_deriv (by simp only [id_eq]; ring)
  have hder : deriv H = fun s => 2 * c ^ 2 * s := funext fun s => (hD s).deriv
  have hD2 : deriv (deriv H) 0 = 2 * c ^ 2 := by
    rw [hder]
    exact (hasDerivAt_const_mul (2 * c ^ 2)).deriv
  refine ⟨H, hH2, by simp [H], hmajor, ?_⟩
  simpa only [hD2, hc2] using le_refl (2 * g.inner (β 0) w w)

theorem exists_squared_distance_upper_support_of_metric_segment
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {p : M} {γ β : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L)
    (hγ : g.IsGeodesicOn γ (Icc 0 1))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = β 0)
    (hsegment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal (|s - t| * L))
    (hβ : g.IsGeodesicOn β {0})
    (hsec : ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ v w : TangentSpace (𝓡 n) (γ t), 0 ≤ D.curvatureTensor (γ t) v w v w) :
    ∃ H : ℝ → ℝ, ContDiffAt ℝ 2 H 0 ∧ H 0 = L ^ 2 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), g.edist p (β s) ≠ ⊤ ∧
        (g.edist p (β s)).toReal ^ 2 ≤ H s) ∧
      deriv (deriv H) 0 ≤ 2 * g.inner (β 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β 0 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β 0 1) := by
  subst p
  have hbase : g.edist (γ 0) (β 0) = ENNReal.ofReal L := by
    simpa [hγ1] using hsegment 0 (by simp) 1 (by simp)
  have hβcc : g.IsGeodesicOn β (Icc (0 : ℝ) 0) := by
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact hβ 0 (by simp)
  obtain ⟨δβ, hδβ, hβbuf'⟩ := geodesic_open_buffer (by norm_num : (0 : ℝ) ≤ 0) hβcc
  have hβbuf : g.IsGeodesicOn β (Ioo (-δβ) δβ) := by
    simpa only [zero_sub, zero_add] using hβbuf'
  by_cases hL0 : L = 0
  · have heq : γ 0 = β 0 := by
      let : LocallyCompactSpace M :=
        ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
      let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      have hd0 : edist (γ 0) (β 0) = 0 := by
        change g.edist (γ 0) (β 0) = 0
        simpa only [hL0, ENNReal.ofReal_zero] using hbase
      exact edist_eq_zero.mp hd0
    obtain ⟨H, hH2, hH0, hmajor, hHsecond⟩ :=
      squared_distance_support_at_base_point g hδβ hβbuf
    refine ⟨H, hH2, ?_, ?_, hHsecond⟩
    · simpa [hL0] using hH0
    · simpa only [heq] using hmajor
  · obtain ⟨δγ, hδγ, hγbuf'⟩ := geodesic_open_buffer (by norm_num : (0 : ℝ) ≤ 1) hγ
    have hγbuf : g.IsGeodesicOn γ (Ioo (-δγ) (1 + δγ)) := by
      simpa only [zero_sub] using hγbuf'
    have hγv := hasDerivAt_center_chart_of_geodesic hγ (by simp : (0 : ℝ) ∈ Icc 0 1)
    have hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (β 0) := by
      intro s hs t ht
      rw [hbase, ← ENNReal.ofReal_mul (abs_nonneg (s - t))]
      exact hsegment s hs t ht
    have hspeed0 : g.tangentNorm (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) = L := by
      have hh := hγbuf.initial_tangentNorm_eq_of_edist_segment hδγ rfl hγv hmin
      have hn : 0 ≤ g.tangentNorm (γ 0)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) := Real.sqrt_nonneg _
      have hhreal := congrArg ENNReal.toReal (hh.trans hbase)
      simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hL] using hhreal
    have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = L :=
      (Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hγ ht (by simp)).trans hspeed0
    let e := δγ / 2
    have he : 0 < e := by dsimp [e]; linarith
    have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-δγ) (1 + δγ)) := by
      intro t ht
      exact (contMDiffAt_of_isGeodesicOn hγbuf ht).contMDiffWithinAt
    have hsubE : Icc (-e) (1 + e) ⊆ Ioo (-δγ) (1 + δγ) := by
      intro t ht
      dsimp [e] at ht
      constructor <;> linarith [ht.1, ht.2]
    let w := mfderiv 𝓘(ℝ, ℝ) (𝓡 n) β 0 1
    obtain ⟨V, hV, hV0, hV1, hindex⟩ := exists_affine_field_with_index_bound
      g D he isOpen_Ioo hγsmooth hsubE w hsec
    have hγsmall : g.IsGeodesicOn γ (Ioo (-e) (1 + e)) :=
      fun t ht => hγbuf t (hsubE (Ioo_subset_Icc_self ht))
    have hsub01 : Icc (0 : ℝ) 1 ⊆ Ioo (-e) (1 + e) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hβv : HasDerivAt (fun s => extChartAt (𝓡 n) (γ 1) (β s)) (V 1) 0 := by
      rw [hγ1, hV1]
      exact hasDerivAt_center_chart_of_geodesic hβbuf ⟨by linarith, hδβ⟩
    obtain ⟨R⟩ := exists_movingEndpointRealization g
      (by norm_num : (0 : ℝ) < 1) isOpen_Ioo hsub01 hγsmall hV hV0
      hδβ hβbuf hγ1.symm hβv
    obtain ⟨H, hH2, hH0, hmajor, hHsecond⟩ :=
      R.exists_energy_support D hsub01 hγsmall hV hspeed hindex
    refine ⟨H, hH2, hH0, hmajor, ?_⟩
    exact hHsecond.trans_eq (congrArg (fun x : M => 2 * g.inner x w w) hγ1)

end PoincareConjecture.M28.Comparison
end
