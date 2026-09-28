import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineArclength
import Mathlib.Topology.Algebra.Order.Archimedean








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]

omit [T3Space M] in
theorem line_geodesic_chart_deriv_ne_zero (g : RiemannianMetric 1 M)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)} (hv0 : v ≠ 0)
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0) (t : ℝ) :
    deriv (fun u => extChartAt (𝓡 1) (γ t) (γ u)) t ≠ 0 := by
  have hspeed : 0 < g.tangentNorm p v := Real.sqrt_pos.mpr (g.pos p v hv0)
  have hnorm := (line_geodesic_chart_speed g hγ
    (hγ.hasDerivAt_chart_at (mem_univ t) (γ t) (mem_extChartAt_source _)).1).trans
    (line_geodesic_speed g hγ hp hv t)
  intro hz
  simp only [hz, tangentNorm, map_zero, Real.sqrt_zero] at hnorm
  exact hspeed.ne' hnorm.symm

omit [T3Space M] in
theorem line_geodesic_mfderiv_bijective (g : RiemannianMetric 1 M)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)} (hv0 : v ≠ 0)
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0) (t : ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t) := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t
  have hne : L 1 ≠ 0 := by
    intro hz
    have hn := line_geodesic_speed g hγ hp hv t
    change L 1 = 0 at hz
    change g.tangentNorm (γ t) (L 1) = g.tangentNorm p v at hn
    simp only [hz, tangentNorm, map_zero, Real.sqrt_zero] at hn
    exact (Real.sqrt_pos.mpr (g.pos p v hv0)).ne' hn.symm
  have hL (r : ℝ) : L r = r • L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul r (1 : ℝ)
  change Function.Bijective L
  constructor
  · intro a b hab
    have hz : (a - b) • L 1 = 0 := by rw [← hL, map_sub, hab, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hne)
  · intro w
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1)
      hne w
    exact ⟨a, (hL a).trans ha⟩


theorem periodic_line_geodesic_of_eq (g : RiemannianMetric 1 M)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)} (hv0 : v ≠ 0)
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0)
    {a b : ℝ} (hab : γ a = γ b) : Function.Periodic γ (b - a) := by
  have hspeed : 0 < g.tangentNorm p v := Real.sqrt_pos.mpr (g.pos p v hv0)
  have hnorm (t : ℝ) :
      g.tangentNorm (γ t) (deriv (fun u => extChartAt (𝓡 1) (γ t) (γ u)) t) =
        g.tangentNorm p v :=
    (line_geodesic_chart_speed g hγ
      (hγ.hasDerivAt_chart_at (mem_univ t) (γ t) (mem_extChartAt_source _)).1).trans
      (line_geodesic_speed g hγ hp hv t)
  have hne := line_geodesic_chart_deriv_ne_zero g hγ hp hv0 hv
  let va := deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) a
  let vb := deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) b
  have hva := (hγ.hasDerivAt_chart_at (mem_univ a) (γ a) (mem_extChartAt_source _)).1
  have hvb := (hγ.hasDerivAt_chart_at (mem_univ b) (γ a)
    (by rw [hab]; exact mem_extChartAt_source _)).1
  obtain ⟨c, hcv⟩ := exists_smul_eq_of_finrank_eq_one
    (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1)
    (hne a) vb
  have hcabs : |c| = 1 := by
    have hna : g.tangentNorm (γ a) va = g.tangentNorm p v := hnorm a
    have hnb : g.tangentNorm (γ a) vb = g.tangentNorm p v := by
      change Real.sqrt (g.inner (γ a) vb vb) = _
      dsimp only [vb]
      rw [hab]
      exact hnorm b
    rw [← hcv] at hnb
    have hsmul : g.tangentNorm (γ a) (c • va) = |c| * g.tangentNorm (γ a) va := by
      simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
    rw [hsmul, hna] at hnb
    exact mul_right_cancel₀ hspeed.ne' (hnb.trans (one_mul _).symm)
  have hleft : g.IsGeodesicOn (fun t => γ (c * t + a)) univ :=
    fun t _ => hγ.comp_affine c a t (mem_univ _)
  have hright : g.IsGeodesicOn (fun t => γ (t + b)) univ :=
    fun t _ => hγ.comp_add b t (mem_univ _)
  have hdleft : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ (c * t + a)))
      (c • va) 0 := by
    have hd : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ t)) va (c * 0 + a) := by
      simpa only [mul_zero, zero_add] using hva
    simpa only [Function.comp_def, id_eq, mul_one] using!
      hd.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul c).add_const a)
  have hdright : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ (t + b))) vb 0 := by
    have hd : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ t)) vb (0 + b) := by
      simpa only [zero_add] using hvb
    simpa only [Function.comp_def, id_eq, one_smul] using!
      hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).add_const b)
  have hall (t : ℝ) : γ (c * t + a) = γ (t + b) :=
    (hleft.eq_nhds_on_of_initial_data hright
      (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected (mem_univ 0) (γ a)
      (by simpa only [mul_zero, zero_add] using mem_extChartAt_source (I := 𝓡 1) (γ a))
      (by simpa only [mul_zero, zero_add] using hab)
      (hdleft.deriv.trans (hcv.trans hdright.deriv.symm)) t (mem_univ t)).self_of_nhds
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hcabs with hc1 | hcm
  · intro t
    have hh := hall (t - a)
    rw [hc1, one_mul] at hh
    convert hh.symm using 1 <;> congr 1 <;> ring
  · exfalso
    let t := (a - b) / 2
    let s := (a + b) / 2
    have hts : c * t + a = s := by dsimp [t, s]; rw [hcm]; ring
    have hts' : t + b = s := by dsimp [t, s]; ring
    let w := deriv (fun u => extChartAt (𝓡 1) (γ s) (γ u)) s
    have hd := (hγ.hasDerivAt_chart_at (mem_univ s) (γ s) (mem_extChartAt_source _)).1
    have hdL : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ (c * u + a)))
        (c • w) t := by
      have hd' : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ u)) w (c * t + a) := by
        simpa only [hts] using hd
      simpa only [Function.comp_def, id_eq, mul_one] using!
        hd'.scomp t (((hasDerivAt_id t).const_mul c).add_const a)
    have hdR : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ (u + b))) w t := by
      have hd' : HasDerivAt (fun u => extChartAt (𝓡 1) (γ s) (γ u)) w (t + b) := by
        simpa only [hts'] using hd
      simpa only [Function.comp_def, id_eq, one_smul] using!
        hd'.scomp t ((hasDerivAt_id t).add_const b)
    have hzero : c • w = w := hdL.unique
      (hdR.congr_of_eventuallyEq (Eventually.of_forall (fun u => congrArg _ (hall u))))
    rw [hcm, neg_one_smul] at hzero
    have hzero' : w + w = 0 := by
      calc
        w + w = (-w) + w := by rw [hzero]
        _ = 0 := neg_add_cancel w
    have htwo : (2 : ℝ) • w = 0 := by simpa only [two_smul] using hzero'
    exact hne s ((smul_eq_zero.mp htwo).resolve_left (by norm_num))



theorem line_geodesic_chart_deriv_eq_of_eq (g : RiemannianMetric 1 M)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)} (hv0 : v ≠ 0)
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0)
    {a b : ℝ} (hab : γ a = γ b) :
    deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) a =
      deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) b := by
  have hper := periodic_line_geodesic_of_eq g hγ hp hv0 hv hab
  have ha := (hγ.hasDerivAt_chart_at (mem_univ a) (γ a) (mem_extChartAt_source _)).1
  have hb := (hγ.hasDerivAt_chart_at (mem_univ b) (γ a)
    (by rw [hab]; exact mem_extChartAt_source _)).1
  have hab' : a + (b - a) = b := by ring
  have hb' : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ t))
      (deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) b) (a + (b - a)) := by
    simpa only [hab'] using hb
  have hshift : HasDerivAt (fun t => extChartAt (𝓡 1) (γ a) (γ (t + (b - a))))
      (deriv (fun t => extChartAt (𝓡 1) (γ a) (γ t)) b) a := by
    simpa only [Function.comp_def, id_eq, one_smul] using!
      hb'.scomp a ((hasDerivAt_id a).add_const (b - a))
  exact ha.unique (hshift.congr_of_eventuallyEq
    (Eventually.of_forall (fun t => congrArg (extChartAt (𝓡 1) (γ a)) (hper t).symm)))



theorem exists_pos_period_line_geodesic [CompactSpace M] [PreconnectedSpace M]
    (g : RiemannianMetric 1 M) (hc : MetricComplete g)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)} (hv0 : v ≠ 0)
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0) :
    ∃ T : ℝ, 0 < T ∧ Function.Periodic γ T := by
  have hsurj := g.surjective_global_line_geodesic hc hγ hp hv0 hv
  have hninj : ¬ Function.Injective γ := by
    intro hi
    let e := Equiv.ofBijective γ ⟨hi, hsurj⟩
    have he : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ e := contMDiff_global_line_geodesic hγ
    have hei := contMDiff_symm_of_line_coordinate e he
      (line_geodesic_chart_deriv_ne_zero g hγ hp hv0 hv)
    have hcompact := isCompact_univ.image hei.continuous
    rw [image_univ, range_eq_univ.mpr e.symm.surjective] at hcompact
    exact noncompact_univ ℝ hcompact
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hninj
  have hper := periodic_line_geodesic_of_eq g hγ hp hv0 hv hab
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr (Ne.symm hne)) with hneg | hpos
  · exact ⟨-(b - a), neg_pos.mpr hneg, hper.neg⟩
  · exact ⟨b - a, hpos, hper⟩

private def periodSubgroup (γ : ℝ → M) : AddSubgroup ℝ where
  carrier := {T | Function.Periodic γ T}
  zero_mem' := Function.periodic_with_period_zero γ
  add_mem' := fun h₁ h₂ => h₁.add_period h₂
  neg_mem' := fun h => h.neg



theorem exists_fundamental_period_line_geodesic [CompactSpace M] [PreconnectedSpace M]
    (g : RiemannianMetric 1 M) (hc : MetricComplete g)
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ univ) {p : M} (hp : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin 1)} (hv0 : v ≠ 0)
    (hv : HasDerivAt (fun t => extChartAt (𝓡 1) p (γ t)) v 0) :
    ∃ T : ℝ, 0 < T ∧ Function.Periodic γ T ∧
      (∀ a b : ℝ, γ a = γ b ↔ a - b ∈ AddSubgroup.zmultiples T) ∧
      ∀ S : ℝ, 0 < S → Function.Periodic γ S → T ≤ S := by
  let P := periodSubgroup γ
  have hmem (t : ℝ) : t ∈ P ↔ γ t = γ 0 := by
    constructor
    · exact Function.Periodic.eq
    · intro ht
      change Function.Periodic γ t
      simpa only [sub_zero] using periodic_line_geodesic_of_eq g hγ hp hv0 hv ht.symm
  have hclosed : IsClosed (P : Set ℝ) := by
    convert isClosed_eq (contMDiff_global_line_geodesic hγ).continuous continuous_const using 1
    ext t
    exact hmem t
  have hndense : ¬ Dense (P : Set ℝ) := by
    intro hd
    have htop : (P : Set ℝ) = univ := hclosed.closure_eq.symm.trans hd.closure_eq
    have heq : γ = fun _ => γ 0 := funext fun t => (hmem t).mp (by
      change t ∈ (P : Set ℝ)
      rw [htop]
      trivial)
    have hne := line_geodesic_chart_deriv_ne_zero g hγ hp hv0 hv 0
    apply hne
    rw [heq]
    exact deriv_const _ _
  obtain ⟨a, ha⟩ := P.dense_or_cyclic.resolve_left hndense
  rw [← AddSubgroup.zmultiples_eq_closure] at ha
  obtain ⟨S, hS, hperS⟩ := exists_pos_period_line_geodesic g hc hγ hp hv0 hv
  have hane : a ≠ 0 := by
    intro hz
    have hSmem : S ∈ AddSubgroup.zmultiples a := ha ▸ hperS
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hSmem
    rw [hz, smul_zero] at hk
    exact hS.ne' hk.symm
  obtain ⟨T, hT, hPT⟩ : ∃ T : ℝ, 0 < T ∧ P = AddSubgroup.zmultiples T := by
    rcases lt_or_gt_of_ne hane with hneg | hpos
    · exact ⟨-a, neg_pos.mpr hneg, ha.trans AddSubgroup.zmultiples_neg.symm⟩
    · exact ⟨a, hpos, ha⟩
  have hper : Function.Periodic γ T := by
    show T ∈ P
    rw [hPT]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, one_smul ℤ T⟩
  refine ⟨T, hT, hper, ?_, ?_⟩
  · intro a b
    constructor
    · intro hab
      rw [← hPT]
      exact periodic_line_geodesic_of_eq g hγ hp hv0 hv hab.symm
    · intro hab
      have hperiod : Function.Periodic γ (a - b) := by rwa [← hPT] at hab
      simpa only [add_sub_cancel] using hperiod b
  · intro S hS hperiod
    have hSmem : S ∈ AddSubgroup.zmultiples T := hPT ▸ hperiod
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hSmem
    have hkpos : (0 : ℤ) < k := by
      by_contra h
      have hkneg : (k : ℝ) ≤ 0 := by exact_mod_cast le_of_not_gt h
      have : k • T ≤ 0 := by simpa only [zsmul_eq_mul] using mul_nonpos_of_nonpos_of_nonneg hkneg hT.le
      linarith
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
    rw [← hk, zsmul_eq_mul]
    nlinarith

end PoincareConjecture.RiemannianMetric
