import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

set_option autoImplicit false

open Filter Set Metric
open scoped Topology

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

def IsRay (ray : ℝ → M) : Prop :=
  ∀ ⦃s : ℝ⦄, 0 ≤ s → ∀ ⦃t : ℝ⦄, 0 ≤ t → dist (ray s) (ray t) = |s - t|

def IsMinimizingOn (curve : ℝ → M) (I : Set ℝ) : Prop :=
  ∀ ⦃s⦄, s ∈ I → ∀ ⦃t⦄, t ∈ I → dist (curve s) (curve t) = |s - t|

def HasMinimizingSegments (M : Type*) [MetricSpace M] : Prop :=
  ∀ x y : M, ∃ curve : ℝ → M, curve 0 = x ∧ curve (dist x y) = y ∧
    IsMinimizingOn curve (Icc 0 (dist x y))

def busemannApprox (ray : ℝ → M) (t : ℝ) (x : M) : ℝ := dist (ray t) x - t

noncomputable def busemann (ray : ℝ → M) (x : M) : ℝ :=
  ⨅ t : Ici (0 : ℝ), busemannApprox ray t x

theorem busemannApprox_antitone {ray : ℝ → M} (hray : IsRay ray) (x : M) :
    AntitoneOn (fun t => busemannApprox ray t x) (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have hd : dist (ray t) (ray s) = t - s := by
    rw [hray ht hs, abs_of_nonneg (sub_nonneg.mpr hst)]
  have h := dist_triangle (ray t) (ray s) x
  rw [hd] at h
  dsimp [busemannApprox]
  linarith

theorem neg_dist_le_busemannApprox {ray : ℝ → M} (hray : IsRay ray)
    (x : M) {t : ℝ} (ht : 0 ≤ t) :
    -dist x (ray 0) ≤ busemannApprox ray t x := by
  have hd : dist (ray 0) (ray t) = t := by
    simpa only [zero_sub, abs_neg, abs_of_nonneg ht] using hray le_rfl ht
  have h := dist_triangle (ray 0) x (ray t)
  rw [hd, dist_comm (ray 0) x, dist_comm x (ray t)] at h
  dsimp [busemannApprox]
  linarith

theorem busemannApprox_bddBelow {ray : ℝ → M} (hray : IsRay ray) (x : M) :
    BddBelow (range fun t : Ici (0 : ℝ) => busemannApprox ray t x) :=
  ⟨-dist x (ray 0), by rintro _ ⟨t, rfl⟩; exact neg_dist_le_busemannApprox hray x t.2⟩

theorem busemann_le_approx {ray : ℝ → M} (hray : IsRay ray)
    (x : M) {t : ℝ} (ht : 0 ≤ t) : busemann ray x ≤ busemannApprox ray t x :=
  ciInf_le (busemannApprox_bddBelow hray x) ⟨t, ht⟩

theorem neg_dist_le_busemann {ray : ℝ → M} (hray : IsRay ray) (x : M) :
    -dist x (ray 0) ≤ busemann ray x :=
  le_ciInf fun t => neg_dist_le_busemannApprox hray x t.2

theorem tendsto_busemannApprox {ray : ℝ → M} (hray : IsRay ray) (x : M) :
    Tendsto (fun t => busemannApprox ray t x) atTop (𝓝 (busemann ray x)) :=
  tendsto_comp_val_Ici_atTop.mp
    (tendsto_atTop_ciInf (Set.antitoneOn_iff_antitone.mp (busemannApprox_antitone hray x))
      (busemannApprox_bddBelow hray x))

theorem lipschitz_busemann {ray : ℝ → M} (hray : IsRay ray) :
    LipschitzWith 1 (busemann ray) := by
  apply LipschitzWith.of_le_add
  intro x y
  have h : busemann ray x - dist x y ≤ busemann ray y := by
    apply le_ciInf
    rintro ⟨t, ht⟩
    have h₁ := busemann_le_approx hray x ht
    have h₂ := dist_triangle (ray t) y x
    rw [dist_comm y x] at h₂
    dsimp [busemannApprox] at h₁ ⊢
    linarith
  linarith

theorem busemann_apply_ray {ray : ℝ → M} (hray : IsRay ray)
    {s : ℝ} (hs : 0 ≤ s) : busemann ray (ray s) = -s := by
  apply le_antisymm
  · simpa only [busemannApprox, dist_self, zero_sub] using busemann_le_approx hray (ray s) hs
  · apply le_ciInf
    rintro ⟨t, ht⟩
    dsimp [busemannApprox]
    rw [hray ht hs]
    linarith [le_abs_self (t - s)]

theorem exists_minimizing_hyperfilter_limit [ProperSpace M]
    {I : Set ℝ} (h0I : (0 : ℝ) ∈ I)
    {J : ℕ → Set ℝ} {curve : ℕ → ℝ → M}
    (hcurve : ∀ k, IsMinimizingOn (curve k) (J k)) (h0J : ∀ k, (0 : ℝ) ∈ J k)
    (hexhaust : ∀ t ∈ I, ∀ᶠ k in atTop, t ∈ J k)
    {K : Set M} (hK : IsCompact K) (hanchor : ∀ k, curve k 0 ∈ K) :
    ∃ ray : ℝ → M, IsMinimizingOn ray I ∧ ray 0 ∈ K ∧
      ∀ t ∈ I, Tendsto (fun k => curve k t) (hyperfilter ℕ : Filter ℕ) (𝓝 (ray t)) := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (curve 0 0)
  have hball : ∀ t ∈ I, ∀ᶠ k in (hyperfilter ℕ : Filter ℕ),
      curve k t ∈ closedBall (curve 0 0) (R + |t|) := by
    intro t ht
    filter_upwards [(hexhaust t ht).filter_mono Nat.hyperfilter_le_atTop] with k hk
    have h₁ : dist (curve k t) (curve k 0) = |t| := by
      simpa only [sub_zero] using hcurve k hk (h0J k)
    have h₂ : dist (curve k 0) (curve 0 0) ≤ R := hR (hanchor k)
    have h₃ := dist_triangle (curve k t) (curve k 0) (curve 0 0)
    rw [mem_closedBall]
    linarith
  have hlimit : ∀ t : ℝ, ∃ x : M,
      t ∈ I → Tendsto (fun k => curve k t) (hyperfilter ℕ : Filter ℕ) (𝓝 x) := by
    intro t
    by_cases ht : t ∈ I
    · obtain ⟨x, _, hx⟩ := (isCompact_closedBall (curve 0 0) (R + |t|)).ultrafilter_le_nhds'
        ((hyperfilter ℕ).map fun k => curve k t) (hball t ht)
      rw [Ultrafilter.coe_map] at hx
      exact ⟨x, fun _ => hx⟩
    · exact ⟨curve 0 0, fun h => absurd h ht⟩
  choose ray hray using hlimit
  refine ⟨ray, ?_, ?_, fun t ht => hray t ht⟩
  · intro s hs t ht
    have h₁ := (hray s hs).dist (hray t ht)
    have h₂ : (fun k => dist (curve k s) (curve k t)) =ᶠ[(hyperfilter ℕ : Filter ℕ)]
        fun _ => |s - t| := by
      filter_upwards [(hexhaust s hs).filter_mono Nat.hyperfilter_le_atTop,
        (hexhaust t ht).filter_mono Nat.hyperfilter_le_atTop] with k hks hkt
      exact hcurve k hks hkt
    exact tendsto_nhds_unique (h₁.congr' h₂) tendsto_const_nhds
  · exact hK.isClosed.mem_of_tendsto (hray 0 h0I) (Eventually.of_forall hanchor)

theorem exists_ray_in_closed_set [ProperSpace M]
    {K : Set M} (hK : IsClosed K) (hnc : ¬ IsCompact K) {p : M}
    (hsegments : ∀ q ∈ K, ∃ curve : ℝ → M, curve 0 = p ∧
      curve (dist p q) = q ∧ IsMinimizingOn curve (Icc 0 (dist p q)) ∧
        MapsTo curve (Icc 0 (dist p q)) K) :
    ∃ ray : ℝ → M, IsRay ray ∧ ray 0 = p ∧ MapsTo ray (Ici 0) K := by
  classical
  have hunbounded : ∀ R : ℝ, ∃ q ∈ K, R ≤ dist p q := by
    intro R
    by_contra! h
    apply hnc
    apply (isCompact_closedBall p R).of_isClosed_subset hK
    intro q hq
    rw [mem_closedBall, dist_comm]
    exact (h q hq).le
  choose q hqK hq using hunbounded
  choose curve hcurve0 hcurved hcurve hcurveK using fun k : ℕ => hsegments (q k) (hqK k)
  have hexhaust : ∀ t ∈ Ici (0 : ℝ), ∀ᶠ k in atTop,
      t ∈ Icc 0 (dist p (q (k : ℕ))) := by
    intro t ht
    filter_upwards [eventually_ge_atTop ⌈t⌉₊] with k hk
    exact ⟨ht, (Nat.le_ceil t).trans ((Nat.cast_le.mpr hk).trans (hq k))⟩
  obtain ⟨ray, hray, hray0, hlimit⟩ := exists_minimizing_hyperfilter_limit
    (I := Ici 0) self_mem_Ici hcurve (fun _ => ⟨le_rfl, dist_nonneg⟩)
      hexhaust isCompact_singleton (fun k => show curve k 0 ∈ ({p} : Set M) from hcurve0 k)
  refine ⟨ray, hray, hray0, ?_⟩
  intro t ht
  apply hK.mem_of_tendsto (hlimit t ht)
  filter_upwards [(hexhaust t ht).filter_mono Nat.hyperfilter_le_atTop] with k hk
  exact hcurveK k hk

end Poincare.Riemannian.Soul
