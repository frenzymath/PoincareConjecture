import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def coordinateChristoffel
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) : E :=
  (B x).inverse (metricKoszulCovector (fderiv ℝ B x) u v)

noncomputable def coordinateGeodesicField
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (z : E × E) : E × E :=
  (z.2, -coordinateChristoffel B z.1 z.2 z.2)

theorem contDiffAt_coordinateGeodesicField
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {z : E × E}
    (hB : ContDiffAt ℝ ∞ B z.1) (hinv : (B z.1).IsInvertible) :
    ContDiffAt ℝ ∞ (coordinateGeodesicField B) z := by
  have hD : ContDiffAt ℝ ∞ (fun p : E × E => fderiv ℝ B p.1) z :=
    (hB.fderiv_right (by simp)).comp z contDiffAt_fst
  have hinverse : ContDiffAt ℝ ∞
      (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.inverse) (B z.1) :=
    hinv.contDiffAt_map_inverse
  have hi : ContDiffAt ℝ ∞ (fun p : E × E => (B p.1).inverse) z := by
    convert! hinverse.comp z (hB.comp z contDiffAt_fst) using 1
  have hflip : ContDiff ℝ ∞ (fun L : E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).contDiff
  have hflip' : ContDiff ℝ ∞
      (fun L : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ => L.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).contDiff
  have hK : ContDiffAt ℝ ∞
      (fun p : E × E => metricKoszulCovector (fderiv ℝ B p.1) p.2 p.2) z := by
    unfold metricKoszulCovector
    exact (((hD.clm_apply contDiffAt_snd).clm_apply contDiffAt_snd).add
      ((hflip.contDiffAt.comp z (hD.clm_apply contDiffAt_snd)).clm_apply
        contDiffAt_snd) |>.sub
      ((hflip.contDiffAt.comp z
        ((hflip'.contDiffAt.comp z hD).clm_apply contDiffAt_snd)).clm_apply
          contDiffAt_snd)).const_smul _
  exact contDiffAt_snd.prodMk (hi.clm_apply hK).neg

omit [CompleteSpace E] in

theorem hasDerivAt_coordinate_geodesic_energy
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q w : ℝ → E} {t : ℝ}
    (hB : DifferentiableAt ℝ B (q t)) (hinv : (B (q t)).IsInvertible)
    (hsymm : ∀ u v, B (q t) u v = B (q t) v u)
    (hq : HasDerivAt q (w t) t)
    (hw : HasDerivAt w (-coordinateChristoffel B (q t) (w t) (w t)) t) :
    HasDerivAt (fun s => B (q s) (w s) (w s)) 0 t := by
  have hE := ((hB.hasFDerivAt.comp_hasDerivAt t hq).clm_apply hw).clm_apply hw
  have hG : B (q t) (coordinateChristoffel B (q t) (w t) (w t)) (w t) =
      (2⁻¹ : ℝ) * (fderiv ℝ B (q t) (w t)) (w t) (w t) := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (w t))
      (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B (q t)) (w t) (w t)))
    simpa [coordinateChristoffel, metricKoszulCovector] using h
  convert! hE using 1
  simp only [Function.comp_apply, add_apply, map_neg, neg_apply]
  rw [hsymm (w t) (coordinateChristoffel B (q t) (w t) (w t)), hG]
  ring

theorem exists_coordinate_geodesic
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hinv : ∀ x ∈ U, (B x).IsInvertible)
    {x : E} (hx : x ∈ U) (v : E) :
    ∃ q w : ℝ → E, ∃ δ : ℝ, 0 < δ ∧ q 0 = x ∧ w 0 = v ∧
      ∀ t ∈ Ioo (-δ) δ, q t ∈ U ∧ HasDerivAt q (w t) t ∧
        HasDerivAt w (-coordinateChristoffel B (q t) (w t) (w t)) t := by
  have hV := contDiffAt_coordinateGeodesicField
    ((hB x hx).contDiffAt (hU.mem_nhds hx)) (hinv x hx) (z := (x, v))
  have hV1 : ContDiffAt ℝ 1 (coordinateGeodesicField B) (x, v) := hV.of_le (by simp)
  obtain ⟨a, ha, ε, hε, hderiv⟩ :=
    hV1.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hd0 := hderiv 0 (by simpa using (show -ε < (0 : ℝ) ∧ 0 < ε by constructor <;> linarith))
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), (a t).1 ∈ U :=
    hd0.continuousAt.fst.preimage_mem_nhds
      (by simpa [ha] using hU.mem_nhds hx)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (hmem.and (Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε))
  refine ⟨fun t => (a t).1, fun t => (a t).2, δ, hδ, ?_, ?_, ?_⟩
  · exact congrArg Prod.fst ha
  · exact congrArg Prod.snd ha
  · intro t ht
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using ht
    obtain ⟨htU, htε⟩ := hδsub htball
    have hd := hderiv t (by simpa using htε)
    exact ⟨htU, hd.fst, hd.snd⟩

theorem exists_coordinate_geodesic_with_energy
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hsymm : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    {x : E} (hx : x ∈ U) (v : E) :
    ∃ q w : ℝ → E, ∃ δ : ℝ, 0 < δ ∧ q 0 = x ∧ w 0 = v ∧
      ∀ t ∈ Ioo (-δ) δ, q t ∈ U ∧ HasDerivAt q (w t) t ∧
        HasDerivAt w (-coordinateChristoffel B (q t) (w t) (w t)) t ∧
        B (q t) (w t) (w t) = B x v v := by
  obtain ⟨q, w, δ, hδ, hq0, hw0, hqw⟩ := exists_coordinate_geodesic hU hB hinv hx v
  have henergy : ∀ t ∈ Ioo (-δ) δ,
      HasDerivAt (fun s => B (q s) (w s) (w s)) 0 t := by
    intro t ht
    obtain ⟨htU, hq, hw⟩ := hqw t ht
    exact hasDerivAt_coordinate_geodesic_energy
      (((hB (q t) htU).contDiffAt (hU.mem_nhds htU)).differentiableAt
        (by simp)) (hinv (q t) htU) (hsymm (q t) htU) hq hw
  refine ⟨q, w, δ, hδ, hq0, hw0, fun t ht => ?_⟩
  refine ⟨(hqw t ht).1, (hqw t ht).2.1, (hqw t ht).2.2, ?_⟩
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-δ) δ).isPreconnected
    (fun s hs => (henergy s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (henergy s hs).deriv) ht
    (show (0 : ℝ) ∈ Ioo (-δ) δ by constructor <;> linarith)
  simpa only [hq0, hw0] using hconst

theorem coordinate_geodesic_unique_germ
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x v : E}
    (hB : ContDiffAt ℝ ∞ B x) (hinv : (B x).IsInvertible)
    {q₁ w₁ q₂ w₂ : ℝ → E}
    (hq₁ : q₁ 0 = x) (hw₁ : w₁ 0 = v) (hq₂ : q₂ 0 = x) (hw₂ : w₂ 0 = v)
    (hd₁ : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt q₁ (w₁ t) t ∧
      HasDerivAt w₁ (-coordinateChristoffel B (q₁ t) (w₁ t) (w₁ t)) t)
    (hd₂ : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt q₂ (w₂ t) t ∧
      HasDerivAt w₂ (-coordinateChristoffel B (q₂ t) (w₂ t) (w₂ t)) t) :
    ∀ᶠ t in 𝓝 (0 : ℝ), q₁ t = q₂ t ∧ w₁ t = w₂ t := by
  have hV := contDiffAt_coordinateGeodesicField hB hinv (z := (x, v))
  obtain ⟨K, S, hS, hLip⟩ := (hV.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
  have hmem₁ : ∀ᶠ t in 𝓝 (0 : ℝ), (q₁ t, w₁ t) ∈ S := by
    apply ((hd₁.self_of_nhds).1.continuousAt.prodMk
      (hd₁.self_of_nhds).2.continuousAt).preimage_mem_nhds
    simpa only [hq₁, hw₁] using hS
  have hmem₂ : ∀ᶠ t in 𝓝 (0 : ℝ), (q₂ t, w₂ t) ∈ S := by
    apply ((hd₂.self_of_nhds).1.continuousAt.prodMk
      (hd₂.self_of_nhds).2.continuousAt).preimage_mem_nhds
    simpa only [hq₂, hw₂] using hS
  have heq := ODE_solution_unique_of_eventually
    (v := fun _ : ℝ => coordinateGeodesicField B) (s := fun _ : ℝ => S)
    (K := K) (t₀ := 0) (Eventually.of_forall (fun _ => hLip))
    (hd₁.and hmem₁ |>.mono fun t ht => ⟨ht.1.1.prodMk ht.1.2, ht.2⟩)
    (hd₂.and hmem₂ |>.mono fun t ht => ⟨ht.1.1.prodMk ht.1.2, ht.2⟩)
    (show (q₁ 0, w₁ 0) = (q₂ 0, w₂ 0) by rw [hq₁, hw₁, hq₂, hw₂])
  exact heq.mono fun t ht => ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩

end PoincareConjecture

namespace PoincareConjecture.RiemannianMetric

open scoped Manifold

theorem exists_chart_geodesic
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    ∃ q w : ℝ → EuclideanSpace ℝ (Fin n), ∃ δ : ℝ,
      0 < δ ∧ q 0 = c p ∧ w 0 = v ∧
      ∀ t ∈ Ioo (-δ) δ, q t ∈ c.target ∧ HasDerivAt q (w t) t ∧
        HasDerivAt w (-coordinateChristoffel B (q t) (w t) (w t)) t ∧
        B (q t) (w t) (w t) = B (c p) v v := by
  exact exists_coordinate_geodesic_with_energy (isOpen_extChartAt_target (I := 𝓡 n) p)
    (g.contDiffOn_chartCoefficients p) (fun x hx => g.isInvertible_chartCoefficients p hx)
    (fun x _ u w => g.symm _ _ _) (mem_extChartAt_target p) v

end PoincareConjecture.RiemannianMetric
