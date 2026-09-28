import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M04.ShiPathCarrier

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set Filter Topology

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem exists_contMDiff_path_length_lt_cap
    (g : RiemannianMetric n M) {x y : M} {L : ℝ≥0∞}
    (hxy : g.edist x y < L) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ ∧ g.pathELength γ 0 1 < L := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hL, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hxy zero_lt_one
  exact ⟨γ, h0, h1, hγ, hL⟩

private theorem shi_edist_le_mul_edist
    (g h : RiemannianMetric n M) (p q : M) {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hq : q ∈ g.ball p R)
    (hcomp : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm x v ≤ C * g.tangentNorm x v) :
    h.edist p q ≤ ENNReal.ofReal C * g.edist p q := by
  have hqfin : g.edist p q ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_lt (show g.edist p q < ENNReal.ofReal R from hq)
  let d : ℝ := (g.edist p q).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hdR : d < R := ENNReal.toReal_lt_of_lt_ofReal hq
  have hpath (ε : ℝ) (hε : 0 < ε) (hεR : d + ε < R) :
      h.edist p q ≤ ENNReal.ofReal (C * (d + ε)) := by
    have hlt : g.edist p q < ENNReal.ofReal (d + ε) := by
      calc
        g.edist p q = ENNReal.ofReal d := (ENNReal.ofReal_toReal hqfin).symm
        _ < ENNReal.ofReal (d + ε) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
      exists_contMDiff_path_length_lt_cap g hlt
    have hmap : MapsTo γ (Icc 0 1) (g.ball p R) := by
      apply mapsTo_ball_of_pathELength_lt g p (r := R) (a := 0) (b := 1)
        zero_le_one hγsmooth.contMDiffOn hγ0
      exact hγlen.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    have hlen := pathELength_le_of_tangentNorm_le h g hC hcomp γ hmap
    have hed : h.edist (γ 0) (γ 1) ≤ h.pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨h.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength
        hγsmooth.contMDiffOn rfl rfl zero_le_one
    have hsum : h.edist p q ≤ ENNReal.ofReal C * ENNReal.ofReal (d + ε) := by
      calc
        h.edist p q ≤ h.pathELength γ 0 1 := by simpa [hγ0, hγ1] using hed
        _ ≤ ENNReal.ofReal C * g.pathELength γ 0 1 := hlen
        _ ≤ ENNReal.ofReal C * ENNReal.ofReal (d + ε) :=
          mul_le_mul_of_nonneg_left hγlen.le zero_le
    simpa only [ENNReal.ofReal_mul hC] using hsum
  have hε : ∀ j : ℕ, 0 < (R - d) / 2 * (1 / ((j : ℝ) + 1)) := by
    intro j; positivity
  have hεR (j : ℕ) : d + (R - d) / 2 * (1 / ((j : ℝ) + 1)) < R := by
    have hj : 0 < 1 / ((j : ℝ) + 1) := by positivity
    have hj1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    nlinarith [hdR]
  have hseq : ∀ j : ℕ,
      h.edist p q ≤ ENNReal.ofReal (C * (d + (R - d) / 2 *
        (1 / ((j : ℝ) + 1)))) := fun j => hpath _ (hε j) (hεR j)
  have he : Tendsto (fun j : ℕ => (R - d) / 2 *
      (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds (x := (R - d) / 2)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hreal : Tendsto (fun j : ℕ => C *
      (d + (R - d) / 2 * (1 / ((j : ℝ) + 1)))) atTop (𝓝 (C * d)) :=
    by simpa only [add_zero] using ((he.const_add d).const_mul C)
  have hlim : Tendsto (fun j : ℕ => ENNReal.ofReal (C *
      (d + (R - d) / 2 * (1 / ((j : ℝ) + 1))))) atTop
      (𝓝 (ENNReal.ofReal (C * d))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hlim' : Tendsto (fun j : ℕ => ENNReal.ofReal (C *
      (d + (R - d) / 2 * (1 / ((j : ℝ) + 1))))) atTop
      (𝓝 (ENNReal.ofReal C * g.edist p q)) := by
    simpa only [ENNReal.ofReal_mul hC, d, ENNReal.ofReal_toReal hqfin] using hlim
  exact ge_of_tendsto hlim' (Eventually.of_forall (hseq))

noncomputable def shiCappedDistance
    (g : RiemannianMetric n M) (p : M) (R : ℝ) (x : M) : ℝ :=
  (min (g.edist p x) (ENNReal.ofReal R)).toReal

theorem shiCappedDistance_nonneg {g : RiemannianMetric n M} {p x : M} {R : ℝ}
    (hR : 0 ≤ R) : 0 ≤ shiCappedDistance g p R x := by
  unfold shiCappedDistance
  exact ENNReal.toReal_nonneg

theorem shiCappedDistance_le {g : RiemannianMetric n M} {p x : M} {R : ℝ}
    (hR : 0 ≤ R) : shiCappedDistance g p R x ≤ R := by
  unfold shiCappedDistance
  have hcap : min (g.edist p x) (ENNReal.ofReal R) ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (min_le_right _ _)).trans_eq
    (ENNReal.toReal_ofReal hR)

theorem shiCappedDistance_eq_of_mem_ball {g : RiemannianMetric n M}
    {p x : M} {R : ℝ} (hx : x ∈ g.ball p R) :
    shiCappedDistance g p R x = (g.edist p x).toReal := by
  exact congrArg ENNReal.toReal (min_eq_left hx.le)

theorem shiCappedDistance_eq_of_le_edist {g : RiemannianMetric n M}
    {p x : M} {R : ℝ} (hR : 0 ≤ R) (hx : ENNReal.ofReal R ≤ g.edist p x) :
    shiCappedDistance g p R x = R := by
  simp only [shiCappedDistance, min_eq_right hx, ENNReal.toReal_ofReal hR]

theorem continuous_shiCappedDistance [T2Space M]
    (g : RiemannianMetric n M) (p : M) (R : ℝ) :
    Continuous (shiCappedDistance g p R) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  have hd : Continuous (fun x => g.edist p x) := continuous_const.edist continuous_id
  have hm : Continuous (fun x => min (g.edist p x) (ENNReal.ofReal R)) :=
    hd.min continuous_const
  apply continuous_iff_continuousAt.2
  intro x
  exact ENNReal.continuousAt_toReal (by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)) |>.comp
      (hm.continuousAt)

theorem shiCappedDistance_flow_comparison
    {T K R : ℝ} (F : RicciFlow n M (Icc 0 T)) (hK : 0 ≤ K) (hR : 0 < R)
    (p : M) {U : Set M}
    (hretain : ∀ t ∈ Icc 0 T, (F.metric t).ball p R ⊆ U)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x ∈ U,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : M) :
    shiCappedDistance (F.metric s) p R x ≤
      Real.exp ((n : ℝ) * K * |s - t|) * shiCappedDistance (F.metric t) p R x := by
  have hnorm (y : M) (hy : y ∈ U) (v : TangentSpace (𝓡 n) y) :
      (F.metric s).tangentNorm y v ≤
        Real.exp ((n : ℝ) * K * |s - t|) * (F.metric t).tangentNorm y v := by
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr hst)]
      have h := (tangentNorm_comparison_at_of_curvature_bound F hs ht hst hK y
        (fun τ hτ => hRm τ ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩ y hy) v).1
      have hm := mul_le_mul_of_nonneg_left h
        (Real.exp_pos ((n : ℝ) * K * (t - s))).le
      have he : Real.exp ((n : ℝ) * K * (t - s)) *
          Real.exp (-(n : ℝ) * K * (t - s)) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1; congr 1; ring
      rwa [← mul_assoc, he, one_mul] at hm
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact (tangentNorm_comparison_at_of_curvature_bound F ht hs hts hK y
        (fun τ hτ => hRm τ ⟨ht.1.trans hτ.1, hτ.2.trans hs.2⟩ y hy) v).2
  have he0 : 0 ≤ Real.exp ((n : ℝ) * K * |s - t|) := (Real.exp_pos _).le
  have he1 : 1 ≤ Real.exp ((n : ℝ) * K * |s - t|) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hK) (abs_nonneg _)
  by_cases hx : x ∈ (F.metric t).ball p R
  · have hd := shi_edist_le_mul_edist (F.metric t) (F.metric s) p x hR he0 hx
      (fun y hy v => hnorm y (hretain t ht hy) v)
    have hfin : (F.metric t).edist p x ≠ (⊤ : ℝ≥0∞) := ne_top_of_lt hx
    have hc := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
      ((min_le_left ((F.metric s).edist p x) (ENNReal.ofReal R)).trans hd)
    rw [shiCappedDistance_eq_of_mem_ball hx]
    simpa only [shiCappedDistance, ENNReal.toReal_mul, ENNReal.toReal_ofReal he0] using hc
  · have hx' : ENNReal.ofReal R ≤ (F.metric t).edist p x :=
      le_of_not_gt hx
    rw [shiCappedDistance_eq_of_le_edist hR.le hx']
    exact (shiCappedDistance_le hR.le).trans (by nlinarith)

theorem shiCappedDistance_flow_modulus
    {T K R : ℝ} (F : RicciFlow n M (Icc 0 T)) (hK : 0 ≤ K) (hR : 0 < R)
    (p : M) {U : Set M}
    (hretain : ∀ t ∈ Icc 0 T, (F.metric t).ball p R ⊆ U)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x ∈ U,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : M) :
    |shiCappedDistance (F.metric s) p R x - shiCappedDistance (F.metric t) p R x| ≤
      (Real.exp ((n : ℝ) * K * |s - t|) - 1) * R := by
  have hst := shiCappedDistance_flow_comparison F hK hR p hretain hRm hs ht x
  have hts := shiCappedDistance_flow_comparison F hK hR p hretain hRm ht hs x
  rw [abs_sub_comm t s] at hts
  have he : 0 ≤ Real.exp ((n : ℝ) * K * |s - t|) - 1 := by
    apply sub_nonneg.mpr
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hK) (abs_nonneg _))
  have hb := mul_le_mul_of_nonneg_left
    (shiCappedDistance_le (g := F.metric t) (p := p) (x := x) hR.le) he
  have ha := mul_le_mul_of_nonneg_left
    (shiCappedDistance_le (g := F.metric s) (p := p) (x := x) hR.le) he
  exact abs_le.mpr ⟨by nlinarith only [hts, ha], by nlinarith only [hst, hb]⟩

theorem continuousOn_shiCappedDistance_flow [T2Space M]
    {T K R : ℝ} (F : RicciFlow n M (Icc 0 T)) (hK : 0 ≤ K) (hR : 0 < R)
    (p : M) {U : Set M}
    (hretain : ∀ t ∈ Icc 0 T, (F.metric t).ball p R ⊆ U)
    (hRm : ∀ t ∈ Icc 0 T, ∀ x ∈ U,
      (F.connection t).curvatureTensorNorm x ≤ K) :
    ContinuousOn (fun z : ℝ × M => shiCappedDistance (F.metric z.1) p R z.2)
      (Icc 0 T ×ˢ (univ : Set M)) := by
  intro z hz
  change Tendsto _ (𝓝[Icc 0 T ×ˢ (univ : Set M)] z) (𝓝 _)
  apply tendsto_iff_dist_tendsto_zero.mpr
  have htime : Continuous (fun w : ℝ × M =>
      (Real.exp ((n : ℝ) * K * |w.1 - z.1|) - 1) * R) := by fun_prop
  have hspace : Continuous (fun w : ℝ × M =>
      |shiCappedDistance (F.metric z.1) p R w.2 -
        shiCappedDistance (F.metric z.1) p R z.2|) :=
    ((continuous_shiCappedDistance (F.metric z.1) p R).comp continuous_snd
      |>.sub continuous_const).abs
  have hlim : Tendsto (fun w : ℝ × M =>
      (Real.exp ((n : ℝ) * K * |w.1 - z.1|) - 1) * R +
        |shiCappedDistance (F.metric z.1) p R w.2 -
          shiCappedDistance (F.metric z.1) p R z.2|)
      (𝓝[Icc 0 T ×ˢ (univ : Set M)] z) (𝓝 0) := by
    convert ((htime.add hspace).continuousAt (x := z)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Icc 0 T ×ˢ (univ : Set M))) using 1 <;>
      ext w <;> simp
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hlim
  filter_upwards [self_mem_nhdsWithin] with w hw
  calc
    dist (shiCappedDistance (F.metric w.1) p R w.2)
        (shiCappedDistance (F.metric z.1) p R z.2) ≤
      dist (shiCappedDistance (F.metric w.1) p R w.2)
          (shiCappedDistance (F.metric z.1) p R w.2) +
        dist (shiCappedDistance (F.metric z.1) p R w.2)
          (shiCappedDistance (F.metric z.1) p R z.2) := dist_triangle _ _ _
    _ ≤ _ := by
      simp only [Real.dist_eq]
      exact add_le_add
        (shiCappedDistance_flow_modulus F hK hR p hretain hRm hw.1 hz.1 w.2) le_rfl

end PoincareConjecture.M04
