import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Corners







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField MeasureTheory
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  [MeasurableSpace S] [BorelSpace S] [T3Space S]
  {g : RiemannianMetric 2 S}




theorem gaussBonnet_chartTriangle_of_aligned_frame
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    {e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x}
    (he₁ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source)
    (he₂ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source)
    (hunit₁ : ∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1)
    (hunit₂ : ∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1)
    (horth : ∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0)
    (htriangle : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆ e.target)
    (hpositive : ∀ x ∈ e.source,
      let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) x
      let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1)) x
      0 < g.inner x X (e₁ x) * g.inner x Y (e₂ x) -
        g.inner x X (e₂ x) * g.inner x Y (e₁ x))
    (halign : ∀ x ∈ e.source,
      let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0)) x
      e₁ x = (Real.sqrt (g.inner x X X))⁻¹ • X) :
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
    let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
    let W := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
    let A := e.symm (0, 0)
    let B := e.symm (1, 0)
    let C := e.symm (0, 1)
    (∫ x in e.symm '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1},
      D.scalarCurvature x ∂g.volumeMeasure) +
      2 * ((∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ e₁ X (e.symm (t, 0))) +
        (∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ W V (e.symm (1 - t, t))) -
        (∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ T Y (e.symm (0, t)))) +
      2 * (Real.arccos (g.inner B (e₁ B) (W B)) +
        Real.arccos (g.inner C (W C) (-T C)) +
        Real.arccos (g.inner A (-T A) (e₁ A))) = 4 * Real.pi := by
  dsimp only
  let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
  let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
  let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
  let W := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
  let α := fun x => Real.arccos (g.inner x (T x) (e₁ x))
  let β := fun x => Real.arccos (g.inner x (W x) (e₁ x))
  let A := e.symm (0, 0)
  let B := e.symm (1, 0)
  let C := e.symm (0, 1)
  have hVxy (x : S) : V x = Y x - X x := by
    dsimp only [V, Y, X, mpullback]
    rw [← map_sub]
    congr 1
    change ((-1, 1) : ℝ × ℝ) = (0, 1) - (1, 0)
    ext <;> norm_num
  have hcoord (x : S) (hx : x ∈ e.source) :=
    g.aligned_frame_coordinates x (X := X x) (Y := Y x)
      (hunit₁ x hx) (horth x hx) (halign x hx) (hpositive x hx)
  have hYp (x : S) (hx : x ∈ e.source) : 0 < g.inner x (Y x) (e₂ x) :=
    (hcoord x hx).2.2.2
  have hVp (x : S) (hx : x ∈ e.source) : 0 < g.inner x (V x) (e₂ x) := by
    rw [hVxy]
    simpa only [map_sub, sub_apply, (hcoord x hx).2.2.1, sub_zero] using hYp x hx
  have hA : A ∈ e.source := e.map_target (htriangle (by norm_num))
  have hB : B ∈ e.source := e.map_target (htriangle (by norm_num))
  have hC : C ∈ e.source := e.map_target (htriangle (by norm_num))
  have hcorners (x : S) (hx : x ∈ e.source) :
      Real.arccos (g.inner x (e₁ x) (W x)) = β x ∧
      Real.arccos (g.inner x (W x) (-T x)) = Real.pi + α x - β x ∧
      Real.arccos (g.inner x (-T x) (e₁ x)) = Real.pi - α x := by
    have hc := g.triangle_corner_angles x (hunit₁ x hx) (hunit₂ x hx) (horth x hx)
      (hcoord x hx).1 (hYp x hx)
    have hVeq : Y x - Real.sqrt (g.inner x (X x) (X x)) • e₁ x = V x := by
      rw [← (hcoord x hx).2.1, hVxy]
    simp only [hVeq] at hc
    exact hc.2.2.2.2.2
  have hYedge := D.integral_chart_edge_turning e he hei he₁ he₂ hunit₁ hunit₂ horth
    (0, 0) (0, 1) (by norm_num) (s := 0) (t := 1) (fun r hr => ?_) hYp
  · have hVedge := D.integral_chart_edge_turning e he hei he₁ he₂ hunit₁ hunit₂ horth
      (1, 0) (-1, 1) (by norm_num) (s := 0) (t := 1) (fun r hr => ?_) hVp
    · have hstokes := D.integral_scalarCurvature_chartTriangle e he hei he₁ he₂ hunit₁
        hunit₂ horth hpositive htriangle
      let P := D.surfaceConnectionForm e₁ e₂ X ∘ e.symm
      let Q := D.surfaceConnectionForm e₁ e₂ Y ∘ e.symm
      have hγY (r : ℝ) : ((0, 0) : ℝ × ℝ) + r • (0, 1) = (0, r) := by
        ext <;> simp
      have hγV (r : ℝ) : ((1, 0) : ℝ × ℝ) + r • (-1, 1) = (1 - r, r) := by
        ext <;> simp [sub_eq_add_neg]
      change (∫ r in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ T Y
          (e.symm ((0, 0) + r • (0, 1)))) =
        (∫ r in (0 : ℝ)..1, Q ((0, 0) + r • (0, 1))) +
          α (e.symm ((0, 0) + 1 • (0, 1))) - α (e.symm ((0, 0) + 0 • (0, 1))) at hYedge
      change (∫ r in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ W V
          (e.symm ((1, 0) + r • (-1, 1)))) =
        (∫ r in (0 : ℝ)..1, D.surfaceConnectionForm e₁ e₂ V
          (e.symm ((1, 0) + r • (-1, 1)))) +
          β (e.symm ((1, 0) + 1 • (-1, 1))) - β (e.symm ((1, 0) + 0 • (-1, 1))) at hVedge
      simp only [hγY, hγV, sub_self, sub_zero] at hYedge hVedge
      change (∫ r in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ T Y (e.symm (0, r))) =
        (∫ r in (0 : ℝ)..1, Q (0, r)) + α C - α A at hYedge
      change (∫ r in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ W V (e.symm (1 - r, r))) =
        (∫ r in (0 : ℝ)..1, D.surfaceConnectionForm e₁ e₂ V (e.symm (1 - r, r))) +
          β C - β B at hVedge
      have hbottom : (∫ r in (0 : ℝ)..1,
          D.surfaceTurningForm e₁ e₂ e₁ X (e.symm (r, 0))) =
          ∫ r in (0 : ℝ)..1, P (r, 0) := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hx : e.symm (r, 0) ∈ e.source := by
          apply e.map_target
          apply htriangle
          rw [uIcc_of_le zero_le_one] at hr
          exact ⟨hr.1, le_rfl, by simpa using hr.2⟩
        simp only [surfaceTurningForm, horth _ hx, hunit₁ _ hx, neg_zero,
          zero_smul, one_smul, zero_add]
        rfl
      have hωV (x : S) : D.surfaceConnectionForm e₁ e₂ V x =
          D.surfaceConnectionForm e₁ e₂ Y x - D.surfaceConnectionForm e₁ e₂ X x := by
        simp only [surfaceConnectionForm, covariantDerivativeOnFields, hVxy,
          map_sub, sub_apply]
      have hdiag : (∫ r in (0 : ℝ)..1,
          D.surfaceConnectionForm e₁ e₂ V (e.symm (1 - r, r))) =
          -(∫ r in (0 : ℝ)..1, P (r, 1 - r) - Q (r, 1 - r)) := by
        let f := fun r : ℝ => P (r, 1 - r) - Q (r, 1 - r)
        have hsubst := intervalIntegral.integral_comp_sub_left f (a := 0) (b := 1) 1
        simp only [sub_self, sub_zero] at hsubst
        calc
          _ = ∫ r in (0 : ℝ)..1, -f (1 - r) := by
            apply intervalIntegral.integral_congr
            intro r _
            dsimp only [f, P, Q, Function.comp_apply]
            rw [hωV, show 1 - (1 - r) = r by ring]
            ring
          _ = -(∫ r in (0 : ℝ)..1, f (1 - r)) := intervalIntegral.integral_neg
          _ = _ := congrArg Neg.neg hsubst
      change (∫ x in e.symm '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1},
        D.scalarCurvature x ∂g.volumeMeasure) +
        2 * ((∫ r in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ e₁ X (e.symm (r, 0))) +
          (∫ r in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ W V (e.symm (1 - r, r))) -
          (∫ r in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ T Y (e.symm (0, r)))) +
        2 * (Real.arccos (g.inner B (e₁ B) (W B)) +
          Real.arccos (g.inner C (W C) (-T C)) +
          Real.arccos (g.inner A (-T A) (e₁ A))) = 4 * Real.pi
      rw [hbottom, hVedge, hYedge, hdiag, (hcorners B hB).1,
        (hcorners C hC).2.1, (hcorners A hA).2.2]
      change (∫ x in e.symm '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1},
        D.scalarCurvature x ∂g.volumeMeasure) =
        -2 * ((∫ r in (0 : ℝ)..1, P (r, 0)) -
          (∫ r in (0 : ℝ)..1, P (r, 1 - r) - Q (r, 1 - r)) -
          (∫ r in (0 : ℝ)..1, Q (0, r))) at hstokes
      linarith
    · apply htriangle
      rw [uIcc_of_le zero_le_one] at hr
      change 0 ≤ 1 + r * -1 ∧ 0 ≤ 0 + r * 1 ∧ (1 + r * -1) + (0 + r * 1) ≤ 1
      constructor
      · linarith [hr.2]
      constructor <;> linarith [hr.1]
  · apply htriangle
    rw [uIcc_of_le zero_le_one] at hr
    change 0 ≤ 0 + r * 0 ∧ 0 ≤ 0 + r * 1 ∧ (0 + r * 0) + (0 + r * 1) ≤ 1
    constructor
    · ring_nf; exact le_rfl
    constructor <;> linarith [hr.1, hr.2]



theorem exists_gaussBonnet_chartTriangle
    (D : LeviCivitaData g) (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (he : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target)
    (htriangle : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆ e.target) :
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
    let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
    let W := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
    let A := e.symm (0, 0)
    let B := e.symm (1, 0)
    let C := e.symm (0, 1)
    ∃ e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₁) e.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% e₂) e.source ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x ∈ e.source, g.inner x (e₁ x) (e₂ x) = 0) ∧
      (∀ x ∈ e.source, 0 <
        g.inner x (X x) (e₁ x) * g.inner x (Y x) (e₂ x) -
          g.inner x (X x) (e₂ x) * g.inner x (Y x) (e₁ x)) ∧
      (∀ x ∈ e.source, e₁ x = (Real.sqrt (g.inner x (X x) (X x)))⁻¹ • X x) ∧
      (∫ x in e.symm '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1},
        D.scalarCurvature x ∂g.volumeMeasure) +
        2 * ((∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ e₁ X (e.symm (t, 0))) +
          (∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ W V (e.symm (1 - t, t))) -
          (∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂ T Y (e.symm (0, t)))) +
        2 * (Real.arccos (g.inner B (e₁ B) (W B)) +
          Real.arccos (g.inner C (W C) (-T C)) +
          Real.arccos (g.inner A (-T A) (e₁ A))) = 4 * Real.pi := by
  dsimp only
  obtain ⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp, ha⟩ :=
    exists_aligned_positive_chart_frame g e he hei
  have halign (x : S) (_ : x ∈ e.source) := congrFun ha x
  exact ⟨e₁, e₂, h₁, h₂, hu₁, hu₂, ho, hp, halign,
    D.gaussBonnet_chartTriangle_of_aligned_frame e he hei h₁ h₂ hu₁ hu₂ ho
      htriangle hp halign⟩

end PoincareConjecture.LeviCivitaData
