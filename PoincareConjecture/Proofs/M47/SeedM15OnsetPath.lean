import PoincareConjecture.Proofs.M47.SeedM15ComponentCapture
import PoincareConjecture.Proofs.M47.SeedM15PathPositivity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47

open Proofs.M46

private theorem surgeryPositive_of_time_heq
    {F : SurgeryFlowData.{u}} {s t : ℝ} (hst : s = t)
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hxy : HEq x y)
    (hpos : SurgeryPositiveComponentAt F s x) : SurgeryPositiveComponentAt F t y := by
  subst t
  rw [← eq_of_heq hxy]
  exact hpos



theorem seedM15_onset_path_nonpositive
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (R : M46RegularSpacetimeData W) {T b a S : ℝ}
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (hinterval : Icc (T + b) T ⊆ R.history.generalized.interval)
    (hbased : ∀ h z, z ∈ U → HEq (e.forward 0 h z) z)
    (hT : T ∈ R.history.generalized.interval)
    (center : (R.history.generalized.slice T).carrier) (x0 : U)
    (hcenter : R.history.history.forward T hT center = x0.val)
    (ha : a ∈ Ioc b 0)
    (hnot : ∀ z : U, ¬ SurgeryPositiveComponentAt F (T + a / 1)
      (e.forward a ⟨ha.1.le, ha.2⟩ z.val))
    {endpoint : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 S
      ((R.geometry.sliceIdentification T).identification center).val endpoint)
    {tau : ℝ} (htau : tau ∈ Ioc 0 S) (hbefore : T - tau < T + a / 1) :
    ¬ HistoryPositive R.history.history (path.curve tau) := by
  intro hpositive
  let sigma := -a
  have hsigma : sigma ∈ Icc 0 S := by
    simp only [div_one] at hbefore
    exact ⟨neg_nonneg.mpr ha.2, by dsimp [sigma]; linarith [htau.2]⟩
  have hsigmaTau : sigma ≤ tau := by
    simp only [div_one] at hbefore
    dsimp [sigma]
    linarith
  have hclock : (path.curve sigma).1 = T + a / 1 := by
    have h : (path.curve sigma).1 = T - sigma := path.curve_time sigma hsigma
    simpa only [sigma, sub_neg_eq_add, div_one] using h
  have htime : (path.curve sigma).1 ∈ R.history.generalized.interval := by
    rw [hclock]
    apply hinterval
    simp only [div_one]
    constructor <;> linarith [ha.1, ha.2]
  have hafter : b < -sigma := by simpa only [sigma, neg_neg] using ha.1
  obtain ⟨s, hs, z, hsa, hphysical⟩ := seedM15_component_path_capture R U hcompact e
    hinterval hbased hT center x0 hcenter path hsigma hafter htime
  have heq : s = a := by simpa only [sigma, neg_neg] using hsa
  clear hsa
  subst s
  have hp := seedM15_historyPositive_subpath R path hsigma ⟨htau.1.le, htau.2⟩
    hsigmaTau hpositive
  exact hnot z (surgeryPositive_of_time_heq hclock hphysical (hp htime))

end PoincareConjecture.M47
