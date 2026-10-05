import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceHistory
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Cylinder.BallTopology

/-!
# Constructed six-radius source or actual early cap contact

The finite-event search begins with the whole physical ball. Its long
branch supplies the included generalized cylinder and exact six-radius
terminal image through the selected history. Its other branch retains
the actual cap contact, including a possible zero-age contact.
Source: Morgan--Tian Lemma 17.7 and Claim 17.9, pp. 402-406;
blowup-source-survival.md, Stages S1-S3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareMT.M47

/-- Construct the complete actual source before using curvature estimates.
An early actual cap contact is the only retained obstruction in this result. -/
theorem exists_blowup_six_radius_source_or_cap
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base Q tau R : ℝ}
    (hbase : base ∈ H.generalized.interval) (hQ : 0 < Q)
    (htau : 0 < tau) (hR : 0 < R)
    (hJ : Icc (base - 2 * tau / Q) base ⊆ F.time_domain)
    (x : (F.slice base).carrier) :
    ∃ U : TopologicalSpace.Opens (F.slice base).carrier,
      (U : Set (F.slice base).carrier) = (F.metric base).ball x (6 * R / Real.sqrt Q) ∧
      ∃ p0 : U, p0.val = x ∧
        ((∃ htime : ∀ s ∈ Icc (-tau) 0, base + s / Q ∈ H.generalized.interval,
          ∃ d : GeneralizedFlowCylinder H.generalized (F.slice base) base Q
              (Icc (-tau) 0) U,
            let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
            let j := terminalSourceNormal_terminalMap U p0
              (terminalSourceNormal_historyCylinder H U htime d) h0
            (∀ y : U, j y = y.val) ∧
              (F.metric base).ball (j p0) (6 * R / Real.sqrt Q) ⊆
                range (fun y : U => j y)) ∨
          ∃ (a : ℝ) (ha : a ∈ Icc (-tau) 0),
            ∃ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0) U,
              (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) ∧
              ∃ hT : base + a / Q ∈ F.surgery_times,
                ∀ [Nonempty (F.slice (base + a / Q)).carrier],
                  ∃ i : Fin (F.event (base + a / Q) hT).cap_count,
                    (e.forward a ⟨le_rfl, ha.2⟩ '' (U : Set (F.slice base).carrier) ∩
                      ((F.event (base + a / Q) hT).caps i).carrier).Nonempty) := by
  let U : TopologicalSpace.Opens (F.slice base).carrier :=
    ⟨(F.metric base).ball x (6 * R / Real.sqrt Q), M04.initial_ball_isOpen _ _ _⟩
  have hx : x ∈ U := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice base).carrier → Type _) :=
      ⟨(F.metric base).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) x x < ENNReal.ofReal (6 * R / Real.sqrt Q)
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (div_pos (mul_pos (by norm_num) hR)
      (Real.sqrt_pos.mpr hQ))
  let p0 : U := ⟨x, hx⟩
  refine ⟨U, rfl, p0, rfl, ?_⟩
  have htime : Icc (base + (-2 * tau) / Q) base ⊆ F.time_domain := by
    have heq : base + (-2 * tau) / Q = base - 2 * tau / Q := by ring
    rw [heq]
    exact hJ
  obtain ⟨a, ha, e, hbased, hstop⟩ := exists_normalized_open_region_search F hQ
    (by linarith only [htau] : -2 * tau ≤ 0) htime U U.isOpen ⟨x, hx⟩
  by_cases hlong : a < -tau
  · obtain ⟨htime, d, _hmaps, _hmetric, hidentity, hrange⟩ :=
      exists_regular_history_search_interior H hbase htau hlong U p0 e hbased
    refine Or.inl ⟨htime, d, hidentity, ?_⟩
    rw [hrange, hidentity p0]
    exact Subset.refl _
  · have hshort : a ∈ Icc (-tau) 0 := ⟨le_of_not_gt hlong, ha.2⟩
    have hcap := hstop.resolve_left (by
      intro hstart
      have : a < -tau := by rw [hstart]; linarith only [htau]
      exact hlong this)
    exact Or.inr ⟨a, hshort, e, hbased, hcap⟩

end PoincareMT.M47
