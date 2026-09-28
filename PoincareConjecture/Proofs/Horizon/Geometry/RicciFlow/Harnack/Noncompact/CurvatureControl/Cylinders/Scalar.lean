import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ThresholdPointPicking
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Confinement
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_scalarCurvature_fixed_cylinder
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a t₀ : ℝ} (hm : 0 < m) (hJ : Icc a t₀ ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a t₀, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a t₀, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (p : M) (r : ℝ) {L α : ℝ} (hL : 0 < L) (hα : 0 < α)
    (hscale : (4 * ((m + 1 : ℕ) : ℝ) + 32) * α ≤ L)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a t₀) {x₁ : M}
    (hx₁ : x₁ ∈ (F.metric t₁).ball p r)
    (hthreshold : α ≤ (F.connection t₁).scalarCurvature x₁ * (t₁ - a))
    (hmargin : ((F.metric t₁).edist p x₁).toReal +
      2 * L / Real.sqrt ((F.connection t₁).scalarCurvature x₁) < r) :
    ∃ τ ∈ Icc a t₁, ∃ y ∈ (F.metric τ).ball p r,
      ∃ Q : ℝ, Q = (F.connection τ).scalarCurvature y ∧
        0 < Q ∧ (F.connection t₁).scalarCurvature x₁ ≤ Q ∧
        α ≤ Q * (τ - a) ∧
        ((F.metric τ).edist p y).toReal + 2 * L / Real.sqrt Q ≤
          ((F.metric t₁).edist p x₁).toReal +
            2 * L / Real.sqrt ((F.connection t₁).scalarCurvature x₁) ∧
        ∀ s ∈ Icc (τ - α / (2 * Q)) τ, ∀ z : M,
          (F.metric τ).edist y z ≤ ENNReal.ofReal (L / (4 * Real.sqrt Q)) →
          (F.connection s).scalarCurvature z ≤ 4 * Q := by
  have hRic (t : ℝ) (ht : t ∈ Icc a t₀) (x : M)
      (v : TangentSpace (𝓡 (m + 1)) x) : 0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t)) x (hoperator t ht x) v).1
  have ht₀ : t₀ ∈ Icc a t₀ := ⟨ht₁.1.trans ht₁.2, le_rfl⟩
  obtain ⟨τ, hτ, y, hy, Q, hQeq, hQ, hQ₁, hthresholdQ, hrad, hlocal⟩ :=
    exists_scalarCurvature_threshold_point_with_radius_control hC F hJ
      (hcomplete t₀ ht₀) hRic p r hL.le hα ht₁ hx₁ hthreshold
  refine ⟨τ, hτ, y, hy, Q, hQeq, hQ, hQ₁, hthresholdQ, hrad, ?_⟩
  let q := Real.sqrt Q
  let d := ((F.metric τ).edist p y).toReal
  let R := d + L / q
  let r₀ := d + L / (4 * q)
  let a' := τ - α / (2 * Q)
  have hq : 0 < q := Real.sqrt_pos.mpr hQ
  have hq2 : q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hR : 0 < R := by dsimp only [R]; positivity
  have hr₀ : 0 ≤ r₀ := by dsimp only [r₀]; positivity
  have hτ₀ : τ ∈ Icc a t₀ := ⟨hτ.1, hτ.2.trans ht₁.2⟩
  have htime : α / (2 * Q) ≤ τ - a := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Q)).mpr
    nlinarith [mul_nonneg hQ.le (sub_nonneg.mpr hτ.1)]
  have ha' : a ≤ a' := by dsimp only [a']; linarith
  have ha'τ : a' ≤ τ := sub_le_self _ (by positivity)
  have hsub : Icc a' τ ⊆ Icc a t₀ :=
    Icc_subset_Icc ha' hτ₀.2
  have hRr : R < r := by
    have hmarginQ := hrad.trans_lt hmargin
    have hLq : 0 < L / q := div_pos hL hq
    change d + 2 * L / q < r at hmarginQ
    rw [mul_div_assoc] at hmarginQ
    dsimp only [R]
    linarith
  have hRicUpper (s : ℝ) (hs : s ∈ Icc a' τ) (z : M)
      (hz : z ∈ (F.metric s).ball p R) (v : TangentSpace (𝓡 (m + 1)) z) :
      (F.connection s).ricci z v v ≤ (4 * Q) * (F.metric s).inner z v v := by
    have hzreal : ((F.metric s).edist p z).toReal < R := by
      exact (ENNReal.toReal_lt_of_lt_ofReal hz)
    have hzball : z ∈ (F.metric s).ball p r :=
      hz.trans_le (ENNReal.ofReal_le_ofReal hRr.le)
    have hscalar := hlocal s hs z hzball hzreal.le
    have h := ((F.connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric s) (F.connection s)) z
        (hoperator s (hsub hs) z) v).2
    have hinner : 0 ≤ (F.metric s).inner z v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric s).pos z v hv).le
    exact h.trans (mul_le_mul_of_nonneg_right hscalar hinner)
  have hgap : r₀ + (4 * ((m + 1 : ℕ) : ℝ) * q + 8 * (4 * Q) / q) * (τ - a') < R := by
    have heq : (4 * ((m + 1 : ℕ) : ℝ) * q + 8 * (4 * Q) / q) * (τ - a') =
        (4 * ((m + 1 : ℕ) : ℝ) + 32) * α / (2 * q) := by
      dsimp only [a']
      rw [← hq2]
      field_simp
      ring
    rw [heq]
    have hbound := div_le_div_of_nonneg_right hscale (by positivity : 0 ≤ 2 * q)
    have hstrict : L / (4 * q) + L / (2 * q) < L / q := by
      field_simp
      nlinarith
    dsimp only [r₀, R]
    linarith
  intro s hs z hz
  have hpz : (F.metric τ).edist p z ≤ ENNReal.ofReal r₀ := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨(F.metric τ).toRiemannianMetric⟩
    have hyfinite : (F.metric τ).edist p y ≠ ⊤ := ne_top_of_lt hy
    calc
      (F.metric τ).edist p z ≤ (F.metric τ).edist p y + (F.metric τ).edist y z :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal d + ENNReal.ofReal (L / (4 * q)) := by
        rw [ENNReal.ofReal_toReal hyfinite]
        exact _root_.add_le_add le_rfl hz
      _ = ENNReal.ofReal r₀ := (ENNReal.ofReal_add hd (by positivity)).symm
  obtain ⟨_, hzR⟩ := terminal_closedBall_distance_bound hC F hm ha'τ (hsub.trans hJ)
    (fun t ht => hcomplete t (hsub ht)) (fun t ht => hRic t (hsub ht)) p
    (by positivity : 0 ≤ 4 * Q) hq hr₀ hRicUpper hgap s hs z hpz
  have hzball : z ∈ (F.metric s).ball p r :=
    hzR.trans_le (ENNReal.ofReal_le_ofReal hRr.le)
  exact hlocal s hs z hzball (ENNReal.toReal_lt_of_lt_ofReal hzR).le

theorem exists_scalarCurvature_large_cylinder
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a t₀ : ℝ} (hm : 0 < m) (hJ : Icc a t₀ ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a t₀, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a t₀, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (p : M) {r A : ℝ} (hr : 0 < r) (hA : 0 < A)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a t₀) {x₁ : M}
    (hx₁ : (F.metric t₁).edist p x₁ ≤ ENNReal.ofReal (r / 4))
    (hlarge : (64 * (((m + 1 : ℕ) : ℝ) + 8) * A / r) ^ 2 <
      (F.connection t₁).scalarCurvature x₁)
    (hthreshold : 2 * A ≤ (F.connection t₁).scalarCurvature x₁ * (t₁ - a)) :
    ∃ τ ∈ Icc a t₁, ∃ y ∈ (F.metric τ).ball p (r / 2),
      ∃ Q : ℝ, Q = (F.connection τ).scalarCurvature y ∧
        0 < Q ∧ (F.connection t₁).scalarCurvature x₁ ≤ Q ∧
        2 * A ≤ Q * (τ - a) ∧
        ∀ s ∈ Icc (τ - A / Q) τ, ∀ z : M,
          (F.metric τ).edist y z ≤ ENNReal.ofReal (A / Real.sqrt Q) →
          (F.connection s).scalarCurvature z ≤ 4 * Q := by
  let L := 8 * (((m + 1 : ℕ) : ℝ) + 8) * A
  have hL : 0 < L := by dsimp only [L]; positivity
  have hR₁ : 0 < (F.connection t₁).scalarCurvature x₁ :=
    (sq_nonneg _).trans_lt hlarge
  have hq₁ : 0 < Real.sqrt ((F.connection t₁).scalarCurvature x₁) :=
    Real.sqrt_pos.mpr hR₁
  have hseed : 8 * L / r < Real.sqrt ((F.connection t₁).scalarCurvature x₁) := by
    have hbase : 0 ≤ 8 * L / r := by positivity
    have hsq : (8 * L / r) ^ 2 < (F.connection t₁).scalarCurvature x₁ := by
      convert hlarge using 1
      dsimp only [L]
      ring
    nlinarith [Real.sq_sqrt hR₁.le]
  have hbudget : 2 * L / Real.sqrt ((F.connection t₁).scalarCurvature x₁) < r / 4 := by
    have h := (div_lt_iff₀ hr).mp hseed
    apply (div_lt_iff₀ hq₁).mpr
    nlinarith
  have hdist : ((F.metric t₁).edist p x₁).toReal ≤ r / 4 := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r / 4)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hx₁
  have hxball : x₁ ∈ (F.metric t₁).ball p r :=
    hx₁.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  have hmargin : ((F.metric t₁).edist p x₁).toReal +
      2 * L / Real.sqrt ((F.connection t₁).scalarCurvature x₁) < r / 2 := by
    linarith
  obtain ⟨τ, hτ, y, hy, Q, hQeq, hQ, hQ₁, hQt, hrad, hlocal⟩ :=
    exists_scalarCurvature_fixed_cylinder hC F hm hJ hcomplete hoperator p r hL
      (by positivity : 0 < 2 * A)
      (by dsimp only [L]; nlinarith : (4 * ((m + 1 : ℕ) : ℝ) + 32) * (2 * A) ≤ L)
      ht₁ hxball hthreshold (hmargin.trans (by linarith))
  have hyhalf : y ∈ (F.metric τ).ball p (r / 2) := by
    have hyfinite : (F.metric τ).edist p y ≠ ⊤ := ne_top_of_lt hy
    have hrad' := hrad.trans_lt hmargin
    have hpos : 0 ≤ 2 * L / Real.sqrt Q := by positivity
    change (F.metric τ).edist p y < ENNReal.ofReal (r / 2)
    rw [← ENNReal.ofReal_toReal hyfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < r / 2)).mpr (by linarith)
  refine ⟨τ, hτ, y, hyhalf, Q, hQeq, hQ, hQ₁, hQt, ?_⟩
  intro s hs z hz
  have htime : 2 * A / (2 * Q) = A / Q := by ring
  have hscale : A / Real.sqrt Q ≤ L / (4 * Real.sqrt Q) := by
    have hfour : 4 * A ≤ L := by
      dsimp only [L]
      nlinarith [mul_nonneg (show 0 ≤ ((m + 1 : ℕ) : ℝ) by positivity) hA.le]
    calc
      A / Real.sqrt Q = (4 * A) / (4 * Real.sqrt Q) := by ring
      _ ≤ L / (4 * Real.sqrt Q) := div_le_div_of_nonneg_right hfour (by positivity)
  exact hlocal s (by rwa [htime]) z (hz.trans (ENNReal.ofReal_le_ofReal hscale))

end PoincareConjecture.RicciFlow
