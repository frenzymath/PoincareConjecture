import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsGaugeRadius
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsMapTension
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsMapRegularity
import PoincareConjecture.Proofs.M03.ConnectionExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge DeTurckNative

theorem exists_raw_native_deturck_gauge
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht₀ : t₀ ∈ Ico 0 T) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ T - t₀ ∧
      ∃ (w : ℝ → ℝ → ℝ)
        (Φ : ℝ → Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞),
        w 0 = 0 ∧
        (∀ t ∈ Icc 0 delta, ∀ x, Φ t x = rawIntrinsicGaugeMap G t₀ w t x) ∧
        (∀ x, Φ 0 x = intrinsicSpatialCoordinate (G.flow.metric t₀) x) ∧
        (∀ t ∈ Icc 0 delta, ∀ r,
          1 / 2 ≤ deriv (mapRadius (w t)) r ∧ |mapRadius (w t) r - r| ≤ 1 / 4) ∧
        (∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ t ∈ Icc 0 delta, ∀ r,
          (1 + |r|) * |deriv (deriv (w t)) r| ≤ C ∧
          (1 + |r|) * |deriv (deriv (deriv (w t))) r| ≤ D) ∧
        (∀ epsilon > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 delta, ∀ r, R ≤ |r| →
          (1 + |r|) * |deriv (w t) r| < epsilon ∧
          (1 + |r|) * |deriv (deriv (w t)) r| < epsilon) ∧
        ContDiffOn ℝ 2 (fun p : ℝ × StandardCapSpace => Φ p.1 p.2)
          (Ioo 0 delta ×ˢ univ) ∧
        ∀ B : LeviCivitaData (intrinsicSpatialMetric (G.flow.metric t₀)
            (hrotation t₀ ⟨ht₀.1, ht₀.2.trans hTlt⟩)
            (G.complete P ⟨ht₀.1, ht₀.2.trans hTlt⟩)),
          ∀ t ∈ Ioo 0 delta,
          ∀ K : LeviCivitaData (gaugePullbackMetric (G.flow.metric (t₀ + t)) (Φ t).symm),
          ∀ x, HasDerivAt (fun a => Φ a x) (-intrinsicDeTurckField K B (Φ t x)) t := by
  classical
  obtain ⟨delta, hd, hdT, w, hw0, _hwc, hs, h23, hend, hjoint, hmapjets, _hinverse, hPDE⟩ :=
    exists_raw_intrinsic_corrected_radial_gauge P H G hrotation hT hTlt ht₀
  have hvalid (t : ℝ) (ht : t ∈ Icc 0 delta) : t₀ + t ∈ Ico 0 G.lifetime := by
    refine ⟨add_nonneg ht₀.1 ht.1, lt_of_le_of_lt ?_ hTlt⟩
    linarith only [ht.2, hdT]
  have hradial (t : ℝ) (ht : t ∈ Icc 0 delta) :
      ∃ Ψ : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞,
        ∀ x, Ψ x = Real.exp (w t ‖x‖) • x := (hs t ht).2.2.2.2.2
  let Ψ (t : ℝ) : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
    if ht : t ∈ Icc 0 delta then Classical.choose (hradial t ht)
    else Diffeomorph.refl (𝓡 3) StandardCapSpace ∞
  let S (t : ℝ) : Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
    if ht : t ∈ Icc 0 delta then
      intrinsicSpatialDiffeomorph (G.flow.metric (t₀ + t))
        (hrotation (t₀ + t) (hvalid t ht)) (G.complete P (hvalid t ht))
    else Diffeomorph.refl (𝓡 3) StandardCapSpace ∞
  let Φ (t : ℝ) := (S t).trans (Ψ t)
  have hΦ (t : ℝ) (ht : t ∈ Icc 0 delta) (x : StandardCapSpace) :
      Φ t x = rawIntrinsicGaugeMap G t₀ w t x := by
    change Ψ t (S t x) = _
    rw [show Ψ t = Classical.choose (hradial t ht) by simp only [Ψ, dif_pos ht],
      Classical.choose_spec (hradial t ht)]
    simp only [S, dif_pos ht]
    rfl
  have hC2 := rawIntrinsicGaugeMap_joint_c2 P G hrotation hTlt ht₀ hdT
    (fun t ht => ⟨(hs t ht).1, (hs t ht).2.1⟩) hjoint
    hmapjets.1 hmapjets.2.1 hmapjets.2.2 hPDE
  refine ⟨delta, hd, hdT, w, Φ, hw0, hΦ, ?_, ?_, h23, hend, ?_, ?_⟩
  · intro x
    rw [hΦ 0 ⟨le_rfl, hd.le⟩, rawIntrinsicGaugeMap]
    simp only [hw0, Pi.zero_apply, Real.exp_zero, one_smul, add_zero]
  · intro t ht
    exact (hs t ht).2.2.2.1
  · exact hC2.congr (fun p hp => hΦ p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2)
  · intro B t ht K x
    have htcc : t ∈ Icc 0 delta := ⟨ht.1.le, ht.2.le⟩
    have htG : t₀ + t ∈ Ioo 0 G.lifetime :=
      ⟨lt_of_lt_of_le ht.1 (le_add_of_nonneg_left ht₀.1), (hvalid t htcc).2⟩
    let DI : LeviCivitaData (intrinsicSpatialMetric (G.flow.metric (t₀ + t))
        (hrotation (t₀ + t) (hvalid t htcc)) (G.complete P (hvalid t htcc))) :=
      Classical.choice (exists_leviCivitaData _)
    have htime := rawIntrinsicGaugeMap_solves_native_harmonic P G hrotation isOpen_Ioo hjoint
      ⟨ht₀.1, ht₀.2.trans hTlt⟩ ht htG (hs t htcc).1 (hs t htcc).2.1
      (hPDE t ht) DI B x
    have heq : rawIntrinsicGaugeMap G t₀ w t = (Φ t : StandardCapSpace → StandardCapSpace) :=
      funext (fun y => (hΦ t htcc y).symm)
    rw [heq, mapTension_eq_neg_pushedDeTurck (G.flow.metric (t₀ + t)) _
      (Φ t) (G.flow.connection (t₀ + t)) B K] at htime
    apply htime.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with a ha
    exact hΦ a ⟨ha.1.le, ha.2.le⟩ x

end PoincareConjecture.M35.Uniqueness
