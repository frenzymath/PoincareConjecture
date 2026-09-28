import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

private theorem local_edist_global {X : Type*} [PseudoEMetricSpace X]
    {γ : ℝ → X} {a b K : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hγ : ContinuousOn γ (Icc a b))
    (hlocal : ∀ x ∈ Ico a b, ∀ᶠ z in 𝓝[>] x,
      edist (γ x) (γ z) ≤ ENNReal.ofReal (K * (z - x))) :
    edist (γ a) (γ b) ≤ ENNReal.ofReal (K * (b - a)) := by
  let S := {x : ℝ | edist (γ a) (γ x) ≤ ENNReal.ofReal (K * (x - a))}
  have hclosed : IsClosed (S ∩ Icc a b) := by
    have hc : ContinuousOn (fun x => (edist (γ a) (γ x),
        ENNReal.ofReal (K * (x - a)))) (Icc a b) :=
      (continuous_edist.comp_continuousOn (continuousOn_const.prodMk hγ)).prodMk
        (ENNReal.continuous_ofReal.comp (continuous_const.mul
          (continuous_id.sub continuous_const))).continuousOn
    rw [inter_comm]
    exact hc.preimage_isClosed_of_isClosed isClosed_Icc
      OrderClosedTopology.isClosed_le'
  have ha : a ∈ S := by simp [S]
  apply hclosed.Icc_subset_of_forall_exists_gt ha ?_ ⟨hab, le_rfl⟩
  intro x hx y hy
  obtain ⟨z, hz, hzlocal⟩ :=
    ((show ∀ᶠ z in 𝓝[>] x, z ∈ Ioc x y from Ioc_mem_nhdsGT hy).and
      (hlocal x hx.2)).exists
  refine ⟨z, ?_, hz⟩
  change edist (γ a) (γ z) ≤ ENNReal.ofReal (K * (z - a))
  calc
    edist (γ a) (γ z) ≤ edist (γ a) (γ x) + edist (γ x) (γ z) :=
      edist_triangle _ _ _
    _ ≤ ENNReal.ofReal (K * (x - a)) + ENNReal.ofReal (K * (z - x)) :=
      add_le_add hx.1 hzlocal
    _ = ENNReal.ofReal (K * (z - a)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hK (sub_nonneg.mpr hx.2.1))
        (mul_nonneg hK (sub_nonneg.mpr hz.1.le))]
      congr 1
      ring

private theorem local_edist_continuous {X : Type*} [PseudoEMetricSpace X]
    {γ : ℝ → X} {s : Set ℝ} {C : ℝ}
    (hlocal : ∀ x ∈ s, ∀ᶠ z in 𝓝[s] x,
      edist (γ x) (γ z) ≤ ENNReal.ofReal (C * |z - x|)) :
    ContinuousOn γ s := by
  intro x hx
  apply EMetric.tendsto_nhds.mpr
  intro ε hε
  have hc : Tendsto (fun z : ℝ => ENNReal.ofReal (C * |z - x|))
      (𝓝[s] x) (𝓝 0) := by
    have hcont : Continuous (fun z : ℝ => ENNReal.ofReal (C * |z - x|)) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul
        (continuous_id.sub continuous_const).abs)
    simpa using (hcont.tendsto x).mono_left (show 𝓝[s] x ≤ 𝓝 x from nhdsWithin_le_nhds)
  filter_upwards [hlocal x hx, (tendsto_order.mp hc).2 ε hε] with z hz hεz
  exact (edist_comm _ _).trans_le hz |>.trans_lt hεz

private theorem local_edist_global_sharp {X : Type*} [PseudoEMetricSpace X]
    {γ : ℝ → X} {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hlocal : ∀ K : ℝ, C < K → ∀ x ∈ Icc a b, ∀ᶠ z in 𝓝[Icc a b] x,
      edist (γ x) (γ z) ≤ ENNReal.ofReal (K * |z - x|)) :
    edist (γ a) (γ b) ≤ ENNReal.ofReal (C * (b - a)) := by
  have hγ : ContinuousOn γ (Icc a b) :=
    local_edist_continuous (hlocal (C + 1) (by linarith))
  have hKbound : ∀ K : ℝ, C < K →
      edist (γ a) (γ b) ≤ ENNReal.ofReal (K * (b - a)) := by
    intro K hK
    apply local_edist_global hab (hC.trans hK.le) hγ
    intro x hx
    have hloc := (hlocal K hK x ⟨hx.1, hx.2.le⟩).filter_mono
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx))
    filter_upwards [hloc, eventually_mem_nhdsWithin] with z hz hzx
    simpa only [abs_of_nonneg (sub_nonneg.mpr (le_of_lt (show x < z from hzx)))] using hz
  have hcont : Continuous (fun K : ℝ => ENNReal.ofReal (K * (b - a))) :=
    ENNReal.continuous_ofReal.comp (continuous_id.mul continuous_const)
  apply ge_of_tendsto ((hcont.tendsto C).mono_left
    (show 𝓝[>] C ≤ 𝓝 C from nhdsWithin_le_nhds))
  filter_upwards [eventually_mem_nhdsWithin] with K hK
  exact hKbound K hK

namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem edist_le_of_speed_le_on_Icc (g : RiemannianMetric n M)
    {γ : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    {a b K : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I)
    (hspeed : ∀ u ∈ Icc a b, g.tangentNorm (γ u)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ u 1) ≤ K) :
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal (K * (b - a)) := by
  have hc := (g.continuousOn_speed_of_contMDiffOn hI hγ).mono hsub
  apply (g.edist_le_ofReal_integral_speed hab
    ((hγ.mono hsub).of_le (by simp)) hc).trans
  apply ENNReal.ofReal_le_ofReal
  have hi := intervalIntegral.integral_mono_on hab
    (hc.intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume a b) hspeed
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hi

theorem eventually_edist_le_mul_of_lt_speed_bound (g : RiemannianMetric n M)
    {γ : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    {x K : ℝ} (hx : x ∈ I)
    (hK : g.tangentNorm (γ x) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ x 1) < K) :
    ∀ᶠ z in 𝓝 x, g.edist (γ x) (γ z) ≤ ENNReal.ofReal (K * |z - x|) := by
  have hc := (g.continuousOn_speed_of_contMDiffOn hI hγ x hx).continuousAt
    (hI.mem_nhds hx)
  have hn : I ∩ {z | g.tangentNorm (γ z)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ z 1) < K} ∈ 𝓝 x :=
    inter_mem (hI.mem_nhds hx) (hc.preimage_mem_nhds (Iio_mem_nhds hK))
  obtain ⟨a, b, hxint, hint⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  filter_upwards [isOpen_Ioo.mem_nhds hxint] with z hz
  rcases le_total x z with hxz | hzx
  · have hsub : Icc x z ⊆ Ioo a b := fun u hu =>
      ⟨hxint.1.trans_le hu.1, hu.2.trans_lt hz.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hxz)]
    exact g.edist_le_of_speed_le_on_Icc hI hγ hxz (fun _ hu => (hint (hsub hu)).1)
      (fun _ hu => (hint (hsub hu)).2.le)
  · have hsub : Icc z x ⊆ Ioo a b := fun u hu =>
      ⟨hz.1.trans_le hu.1, hu.2.trans_lt hxint.2⟩
    have hbound := g.edist_le_of_speed_le_on_Icc hI hγ hzx
      (fun _ hu => (hint (hsub hu)).1) (fun _ hu => (hint (hsub hu)).2.le)
    have hsym : g.edist (γ x) (γ z) = g.edist (γ z) (γ x) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_comm
    rw [hsym, abs_of_nonpos (sub_nonpos.mpr hzx)]
    convert hbound using 1
    congr 1
    ring
end PoincareConjecture.RiemannianMetric

theorem PoincareConjecture.RiemannianMetric.edist_piecewise_curve_le_of_speed_le
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M)
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Icc a b))
    (γneg γpos : ℝ → M) {Ineg Ipos : Set ℝ}
    (hIneg : IsOpen Ineg) (hIpos : IsOpen Ipos)
    (hγneg : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γneg Ineg)
    (hγpos : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γpos Ipos)
    (hdomneg : ∀ t ∈ Icc a b, q t ≤ 0 → t ∈ Ineg)
    (hdompos : ∀ t ∈ Icc a b, 0 ≤ q t → t ∈ Ipos)
    (heq : ∀ t ∈ Icc a b, q t = 0 → γneg t = γpos t)
    (hspeedneg : ∀ t ∈ Icc a b, q t ≤ 0 →
      g.tangentNorm (γneg t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γneg t 1) ≤ C)
    (hspeedpos : ∀ t ∈ Icc a b, 0 ≤ q t →
      g.tangentNorm (γpos t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γpos t 1) ≤ C) :
    let γ := fun t => if q t ≤ 0 then γneg t else γpos t
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal (C * (b - a)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  dsimp only
  apply local_edist_global_sharp (γ := fun t => if q t ≤ 0 then γneg t else γpos t) hab hC
  intro K hK x hx
  change ∀ᶠ z in 𝓝[Icc a b] x,
    g.edist (if q x ≤ 0 then γneg x else γpos x)
      (if q z ≤ 0 then γneg z else γpos z) ≤ ENNReal.ofReal (K * |z - x|)
  by_cases hxneg : q x < 0
  · have hsign : ∀ᶠ z in 𝓝[Icc a b] x, q z < 0 :=
      (hq x hx) (Iio_mem_nhds hxneg)
    have hbound := (g.eventually_edist_le_mul_of_lt_speed_bound hIneg hγneg
      (hdomneg x hx hxneg.le) ((hspeedneg x hx hxneg.le).trans_lt hK)).filter_mono
      (show 𝓝[Icc a b] x ≤ 𝓝 x from nhdsWithin_le_nhds)
    filter_upwards [hsign, hbound] with z hz hboundz
    simpa only [if_pos hxneg.le, if_pos hz.le] using hboundz
  · by_cases hxpos : 0 < q x
    · have hsign : ∀ᶠ z in 𝓝[Icc a b] x, 0 < q z :=
        (hq x hx) (Ioi_mem_nhds hxpos)
      have hbound := (g.eventually_edist_le_mul_of_lt_speed_bound hIpos hγpos
        (hdompos x hx hxpos.le) ((hspeedpos x hx hxpos.le).trans_lt hK)).filter_mono
        (show 𝓝[Icc a b] x ≤ 𝓝 x from nhdsWithin_le_nhds)
      filter_upwards [hsign, hbound] with z hz hboundz
      simpa only [if_neg (not_le.mpr hxpos), if_neg (not_le.mpr hz)] using hboundz
    · have hxzero : q x = 0 := le_antisymm (not_lt.mp hxpos) (not_lt.mp hxneg)
      have hboundneg := (g.eventually_edist_le_mul_of_lt_speed_bound hIneg hγneg
        (hdomneg x hx hxzero.le) ((hspeedneg x hx hxzero.le).trans_lt hK)).filter_mono
        (show 𝓝[Icc a b] x ≤ 𝓝 x from nhdsWithin_le_nhds)
      have hboundpos := (g.eventually_edist_le_mul_of_lt_speed_bound hIpos hγpos
        (hdompos x hx hxzero.ge) ((hspeedpos x hx hxzero.ge).trans_lt hK)).filter_mono
        (show 𝓝[Icc a b] x ≤ 𝓝 x from nhdsWithin_le_nhds)
      filter_upwards [hboundneg, hboundpos] with z hn hp
      by_cases hz : q z ≤ 0
      · simpa only [if_pos hxzero.le, if_pos hz] using hn
      · simpa only [if_pos hxzero.le, if_neg hz, heq x hx hxzero] using hp
