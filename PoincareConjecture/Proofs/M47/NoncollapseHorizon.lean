import PoincareConjecture.Proofs.M47.NoncollapseHorizonTested
import PoincareConjecture.Proofs.M47.SeedSearchAncestors










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem surgeryNoncollapsedOn_closed_horizon
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {a T kappa : ℝ} (haT : a < T)
    (hinterior : SurgeryNoncollapsedOn F (Ico a T) kappa) :
    SurgeryNoncollapsedOn F (Icc a T) kappa := by
  intro t ht htF x hnonpositive r hr hrepsilon e hbased hcurv
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact hinterior t ⟨ht.1, hlt⟩ htF x hnonpositive r hr hrepsilon e hbased hcurv
  · subst t
    apply horizon_tested_volume_of_interior P haT x hr hrepsilon e hbased hcurv
    intro s hs hslt has q hq hqepsilon d hdbased hdcurv
    have hsF : T + s / 1 ∈ F.time_domain :=
      e.time_subset (mem_image_of_mem _ hs)
    have hx : x ∈ (F.metric T).ball x r := by
      change (F.metric T).edist x x < ENNReal.ofReal r
      rw [M36.metric_edist_self]
      exact ENNReal.ofReal_pos.mpr hr
    have hzero : (0 : ℝ) ∈ Icc (-r ^ 2) 0 :=
      ⟨neg_nonpos.mpr (sq_nonneg r), le_rfl⟩
    have hpoint : (⟨T + 0 / 1, e.forward 0 hzero x⟩ :
        (t : ℝ) × (F.slice t).carrier) = ⟨T, x⟩ :=
      Sigma.ext (by simp) (hbased hzero x hx)
    have hend : ¬ SurgeryPositiveComponentAt F (T + 0 / 1) (e.forward 0 hzero x) :=
      (congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
        ¬ SurgeryPositiveComponentAt F p.1 p.2) hpoint).mpr hnonpositive
    have hsnonpositive := seed_search_nonpositive_of_endpoint e hx hs hzero hslt.le hend
    exact hinterior (T + s / 1)
      ⟨has, by simpa only [div_one] using add_lt_of_neg_right T hslt⟩
      hsF (e.forward s hs x) hsnonpositive q hq hqepsilon d hdbased hdcurv



theorem surgeryVolumeControlOn_closed_horizon
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {a T kappa : ℝ} (haT : a < T)
    (hinterior : SurgeryVolumeControlOn F (Ico a T) kappa (fun _ _ => True)) :
    SurgeryVolumeControlOn F (Icc a T) kappa (fun _ _ => True) := by
  intro t ht htF x _ r hr hrepsilon e hbased hcurv
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact hinterior t ⟨ht.1, hlt⟩ htF x trivial r hr hrepsilon e hbased hcurv
  · subst t
    apply horizon_tested_volume_of_interior P haT x hr hrepsilon e hbased hcurv
    intro s hs hslt has q hq hqepsilon d hdbased hdcurv
    exact hinterior (T + s / 1)
      ⟨has, by simpa only [div_one] using add_lt_of_neg_right T hslt⟩
      (e.time_subset (mem_image_of_mem _ hs)) (e.forward s hs x) trivial
      q hq hqepsilon d hdbased hdcurv

end PoincareConjecture.Proofs.M47
