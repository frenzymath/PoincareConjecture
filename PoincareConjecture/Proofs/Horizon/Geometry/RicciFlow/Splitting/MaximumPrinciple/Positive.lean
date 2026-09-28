import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.Endpoint
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.CompactBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.ChartChain.SeedTube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.ChartChain.ScheduledSegments
noncomputable section
open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

open Barrier ChartChain

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem positive_along_chart_path
    {D : Set M} (hD : IsCompact D) (α : M)
    (hchart : D ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) α).source)
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (conn : ∀ t, LeviCivitaData (g t))
    (hgmetric : RiemannianMetric.IsSmoothFamilyOn g J) (hJdiff : UniqueDiffOn ℝ J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {gamma : ℝ → EuclideanSpace ℝ (Fin n)} (hg : ContDiff ℝ ∞ gamma)
    (hpath : ∀ t ∈ Icc a b, ∃ x ∈ interior D, extChartAt (𝓡 n) α x = gamma t)
    {v : M → ℝ → ℝ}
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (D ×ˢ Icc a b))
    (hvs : HeatLowerContacts conn (interior D) (Ioo a b) v)
    (hinit : ∀ x ∈ D, 0 ≤ v x a)
    (hlateral : ∀ x ∈ D, x ∉ interior D → ∀ t ∈ Icc a b, 0 ≤ v x t)
    {p q : M} (hp : p ∈ interior D) (hq : q ∈ D)
    (hstart : extChartAt (𝓡 n) α p = gamma a) (hend : extChartAt (𝓡 n) α q = gamma b)
    (hpos : 0 < v p a) : 0 < v q b := by
  have hvc : ContinuousOn (fun x => v x a) D :=
    hv.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hx, le_rfl, hab.le⟩)
  obtain ⟨ε, r, hε, hr, hseed⟩ := exists_initial_ball_seed (I := 𝓡 n) α hchart hvc hp hpos
  obtain ⟨s, hs, hclear⟩ := exists_lateral_clearance (I := 𝓡 n) hD α hchart hg.continuous hpath
  let rho := min r s
  have hrho : 0 < rho := lt_min hr hs
  have hsource : D ⊆ (extChartAt (𝓡 n) α).source := by
    simpa only [extChartAt_source] using hchart
  let K := Icc a b ×ˢ (extChartAt (𝓡 n) α '' D)
  have hK : IsCompact K := isCompact_Icc.prod
    (hD.image_of_continuousOn ((continuousOn_extChartAt α).mono hsource))
  have hKU : K ⊆ J ×ˢ (extChartAt (𝓡 n) α).target := by
    rintro ⟨t, y⟩ ⟨ht, x, hx, rfl⟩
    exact ⟨hJ ht, (extChartAt (𝓡 n) α).map_source (hsource hx)⟩
  obtain ⟨lam, Lam, H₀, hlam, hLam, hH₀, hQ, hH⟩ :=
    exists_compact_chart_bounds (g := g) (K := K) (gamma := gamma)
      hgmetric hJdiff α hK hKU hg
  apply positive_at_chart_endpoint hD α hchart conn hab hrho hlam hLam hH₀ hε hg
    hv hvs _ hinit _ hlateral _ hq hend
  · intro x hx t ht _
    have hz : (t, extChartAt (𝓡 n) α x) ∈ K :=
      ⟨⟨ht.1.le, ht.2.le⟩, mem_image_of_mem _ (interior_subset hx)⟩
    have hrad := hQ (t, extChartAt (𝓡 n) α x) hz (extChartAt (𝓡 n) α x - gamma t)
    have hrest := hH (t, extChartAt (𝓡 n) α x) hz
    exact ⟨hrad.1, hrad.2, hrest⟩
  · intro x hx hdist
    apply hseed x hx
    rw [hstart]
    exact hdist.trans_le (min_le_left _ _)
  · intro x hx hn t ht
    exact (min_le_right _ _).trans (hclear x hx hn t ht)


theorem positive_of_connected
    {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (conn : ∀ t, LeviCivitaData (g t))
    (hgmetric : RiemannianMetric.IsSmoothFamilyOn g J) (hJdiff : UniqueDiffOn ℝ J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {v : M → ℝ → ℝ}
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (U ×ˢ Icc a b))
    (hvs : HeatLowerContacts conn U (Ioo a b) v)
    (hnonneg : ∀ x ∈ U, ∀ t ∈ Icc a b, 0 ≤ v x t)
    {p q : M} (hp : p ∈ U) (hq : q ∈ U) (hpos : 0 < v p a) :
    0 < v q b := by
  obtain ⟨γ, _, _, ⟨S⟩⟩ := exists_compact_path_subdivision (I := 𝓡 n) hU hconn hp hq
  have hprop : ∀ k : ℕ, k ≤ S.count →
      0 < v (γ (S.cut k)) (timeCut a b S.count k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa only [S.cut_zero, Path.source, timeCut_zero] using hpos
    | succ k ih =>
      intro hk
      let i : Fin S.count := ⟨k, by omega⟩
      let B := S.ball i
      let l := timeCut a b S.count k
      let r := timeCut a b S.count (k + 1)
      have hl : l ∈ Icc a b := timeCut_mem hab S.count_pos (by omega)
      have hr : r ∈ Icc a b := timeCut_mem hab S.count_pos hk
      have hclosed : Icc l r ⊆ Icc a b :=
        fun _ ht => ⟨hl.1.trans ht.1, ht.2.trans hr.2⟩
      have hopen : Ioo l r ⊆ Ioo a b :=
        fun _ ht => ⟨hl.1.trans_lt ht.1, ht.2.trans_le hr.2⟩
      obtain ⟨c, hlt, hc, _, hstart, hend, hpath⟩ := S.scheduled_segment hab i
      have hBU : interior B.domain ⊆ U := interior_subset.trans B.domain_subset
      have hleft : γ (S.cut k) ∈ interior B.domain :=
        B.core_subset_interior (S.left_mem i)
      have hright : γ (S.cut (k + 1)) ∈ B.domain :=
        interior_subset (B.core_subset_interior (S.right_mem i))
      apply positive_along_chart_path B.isCompact_domain B.center B.domain_chart
        conn hgmetric hJdiff hlt (hclosed.trans hJ) hc hpath
        (hv.mono (Set.prod_mono B.domain_subset hclosed))
        (fun x hx t ht => hvs x (hBU hx) t (hopen ht))
        (fun x hx => hnonneg x (B.domain_subset hx) l hl)
        (fun x hx _ t ht => hnonneg x (B.domain_subset hx) t (hclosed ht))
        hleft hright hstart.symm hend.symm (ih (by omega))
  simpa only [S.cut_last, Path.target, timeCut_last a b S.count_pos] using
    hprop S.count le_rfl



theorem positive_of_connected_on_Icc
    {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {g : ℝ → RiemannianMetric n M} (conn : ∀ t, LeviCivitaData (g t))
    {a b : ℝ} (hab : a < b)
    (hg : RiemannianMetric.IsSmoothFamilyOn g (Icc a b))
    {v : M → ℝ → ℝ}
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (U ×ˢ Icc a b))
    (hvs : HeatLowerContacts conn U (Ioo a b) v)
    (hnonneg : ∀ x ∈ U, ∀ t ∈ Icc a b, 0 ≤ v x t)
    {p q : M} (hp : p ∈ U) (hq : q ∈ U) (hpos : 0 < v p a) :
    0 < v q b :=
  positive_of_connected hU hconn conn hg (uniqueDiffOn_Icc hab) hab Subset.rfl
    hv hvs hnonneg hp hq hpos



theorem eq_zero_before_of_eq_zero
    {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {g : ℝ → RiemannianMetric n M} (conn : ∀ t, LeviCivitaData (g t))
    {a b : ℝ} (hab : a < b)
    (hg : RiemannianMetric.IsSmoothFamilyOn g (Icc a b))
    {v : M → ℝ → ℝ}
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (U ×ˢ Icc a b))
    (hvs : HeatLowerContacts conn U (Ioo a b) v)
    (hnonneg : ∀ x ∈ U, ∀ t ∈ Icc a b, 0 ≤ v x t)
    {q : M} (hq : q ∈ U) (hzero : v q b = 0)
    {t : ℝ} (ht : t ∈ Ico a b) {p : M} (hp : p ∈ U) : v p t = 0 := by
  apply le_antisymm _ (hnonneg p hp t ⟨ht.1, ht.2.le⟩)
  by_contra hn
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
  have hpos := positive_of_connected hU hconn conn hg (uniqueDiffOn_Icc hab) ht.2 hsub
    (hv.mono (prod_mono_right hsub))
    (fun x hx s hs => hvs x hx s ⟨ht.1.trans_lt hs.1, hs.2⟩)
    (fun x hx s hs => hnonneg x hx s (hsub hs)) hp hq (lt_of_not_ge hn)
  exact (ne_of_gt hpos) hzero



theorem eq_zero_on_Icc_of_eq_zero
    {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {g : ℝ → RiemannianMetric n M} (conn : ∀ t, LeviCivitaData (g t))
    {a b : ℝ} (hab : a < b)
    (hg : RiemannianMetric.IsSmoothFamilyOn g (Icc a b))
    {v : M → ℝ → ℝ}
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (U ×ˢ Icc a b))
    (hvs : HeatLowerContacts conn U (Ioo a b) v)
    (hnonneg : ∀ x ∈ U, ∀ t ∈ Icc a b, 0 ≤ v x t)
    {q : M} (hq : q ∈ U) (hzero : v q b = 0)
    {t : ℝ} (ht : t ∈ Icc a b) {p : M} (hp : p ∈ U) : v p t = 0 := by
  have hbefore : ∀ s ∈ Ico a b, v p s ≤ 0 := by
    intro s hs
    exact (eq_zero_before_of_eq_zero hU hconn conn hab hg hv hvs hnonneg hq hzero hs hp).le
  have hc : ContinuousOn (v p) (Icc a b) :=
    hv.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hp, hs⟩)
  have hclosed := le_on_closure hbefore
    (show ContinuousOn (v p) (closure (Ico a b)) by simpa [closure_Ico hab.ne] using hc)
    (show ContinuousOn (fun _ : ℝ => (0 : ℝ)) (closure (Ico a b)) from continuousOn_const)
  exact le_antisymm (hclosed (by simpa [closure_Ico hab.ne] using ht)) (hnonneg p hp t ht)



theorem eq_zero_at_positive_time_iff
    {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {g : ℝ → RiemannianMetric n M} (conn : ∀ t, LeviCivitaData (g t))
    {a b : ℝ} (hg : RiemannianMetric.IsSmoothFamilyOn g (Icc a b))
    {v : M → ℝ → ℝ}
    (hv : ContinuousOn (fun z : M × ℝ => v z.1 z.2) (U ×ˢ Icc a b))
    (hvs : HeatLowerContacts conn U (Ioo a b) v)
    (hnonneg : ∀ x ∈ U, ∀ t ∈ Icc a b, 0 ≤ v x t)
    {t : ℝ} (ht : t ∈ Ioc a b) {p q : M} (hp : p ∈ U) (hq : q ∈ U) :
    v p t = 0 ↔ v q t = 0 := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hg' : RiemannianMetric.IsSmoothFamilyOn g (Icc a t) :=
    hg.mono (prod_mono_left hsub)
  have hv' := hv.mono (prod_mono_right hsub)
  have hvs' : HeatLowerContacts conn U (Ioo a t) v :=
    fun x hx s hs => hvs x hx s ⟨hs.1, hs.2.trans_le ht.2⟩
  have hn' : ∀ x ∈ U, ∀ s ∈ Icc a t, 0 ≤ v x s :=
    fun x hx s hs => hnonneg x hx s (hsub hs)
  constructor
  · intro hz
    exact eq_zero_on_Icc_of_eq_zero hU hconn conn ht.1 hg' hv' hvs' hn' hp hz
      ⟨ht.1.le, le_rfl⟩ hq
  · intro hz
    exact eq_zero_on_Icc_of_eq_zero hU hconn conn ht.1 hg' hv' hvs' hn' hq hz
      ⟨ht.1.le, le_rfl⟩ hp

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
