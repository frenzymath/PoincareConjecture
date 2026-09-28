import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import PoincareConjecture.Proofs.M63.Mathlib.FiniteOrderCompactExtension
import PoincareConjecture.Proofs.M63.Mathlib.C2SecondDerivComposition
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M63

theorem exists_periodic_smooth_fixed_C2_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {P : E → E} (hP : ContDiffOn ℝ ∞ P U)
    (hPU : MapsTo P U U) (hPP : ∀ x ∈ U, P (P x) = P x)
    {L : ℝ} (hL : 0 < L) {c : ℝ → E} (hc : ContDiff ℝ 2 c)
    (hp : Function.Periodic c L) (hcU : range c ⊆ U) (hfix : ∀ x, P (c x) = c x)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ r : ℝ → E, ContDiff ℝ ∞ r ∧ Function.Periodic r L ∧
      (∀ x, r x ∈ U ∧ P (r x) = r x) ∧
      ∀ x, ‖r x - c x‖ < eps ∧ ‖deriv r x - deriv c x‖ < eps ∧
        ‖deriv (deriv r) x - deriv (deriv c) x‖ < eps := by
  let : Fact (0 < L) := ⟨hL⟩
  have hK : IsCompact (range c) := hp.compact_of_continuous hL.ne' hc.continuous
  obtain ⟨G, hG, _hGc, O, hO, hKO, hOU, hGP⟩ :=
    exists_finiteOrder_compact_extension 2 hK hU hcU P
      (hP.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  have hDDG : Continuous (fderiv ℝ (fderiv ℝ G)) :=
    (hG.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  let Phi : C(E × E × E, E × E × E) :=
    ⟨fun z => (G z.1, fderiv ℝ G z.1 z.2.1,
        fderiv ℝ (fderiv ℝ G) z.1 z.2.1 z.2.1 + fderiv ℝ G z.1 z.2.2),
      (G.continuous.comp continuous_fst).prodMk
        (((hDG.comp continuous_fst).clm_apply (continuous_fst.comp continuous_snd)).prodMk
          ((((hDDG.comp continuous_fst).clm_apply
            (continuous_fst.comp continuous_snd)).clm_apply
              (continuous_fst.comp continuous_snd)).add
                ((hDG.comp continuous_fst).clm_apply (continuous_snd.comp continuous_snd))))⟩
  let jet (d : ℝ → E) (hd : ContDiff ℝ 2 d) (hdp : Function.Periodic d L) :
      C(AddCircle L, E × E × E) := by
    have hd1 : ContDiff ℝ 1 (deriv d) := hd.deriv' (n := 1)
    have hp1 := hdp.deriv_of_differentiable (hd.differentiable (by norm_num))
    have hp2 := hp1.deriv_of_differentiable (hd1.differentiable (by norm_num))
    let J := fun x => (d x, deriv d x, deriv (deriv d) x)
    have hJ : Function.Periodic J L := by
      intro x
      dsimp only [J]
      rw [hdp x, hp1 x, hp2 x]
    exact ⟨hJ.lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
        (hd.continuous.prodMk (hd1.continuous.prodMk hd1.continuous_deriv_one))⟩
  have hjet (d : ℝ → E) (hd : ContDiff ℝ 2 d) (hdp : Function.Periodic d L) (x : ℝ) :
      jet d hd hdp (x : AddCircle L) = (d x, deriv d x, deriv (deriv d) x) := rfl
  have hPhi (d : ℝ → E) (hd : ContDiff ℝ 2 d) (hdp : Function.Periodic d L) (x : ℝ) :
      Phi (jet d hd hdp (x : AddCircle L)) =
        ((G ∘ d) x, deriv (G ∘ d) x, deriv (deriv (G ∘ d)) x) := by
    rw [hjet d hd hdp x]
    have hfirst := ((hG.differentiable (by norm_num) (d x)).hasFDerivAt.comp_hasDerivAt
      x (hd.differentiable (by norm_num) x).hasDerivAt).deriv
    have hsecond : deriv (deriv (G ∘ d)) x =
        fderiv ℝ (fderiv ℝ G) (d x) (deriv d x) (deriv d x) +
          fderiv ℝ G (d x) (deriv (deriv d) x) :=
      secondDeriv_comp_of_contDiffAt_two G d x hG.contDiffAt hd.contDiffAt
    change (G (d x), fderiv ℝ G (d x) (deriv d x),
      fderiv ℝ (fderiv ℝ G) (d x) (deriv d x) (deriv d x) +
        fderiv ℝ G (d x) (deriv (deriv d) x)) = _
    rw [hfirst, hsecond, Function.comp_apply]
  let Jc := jet c hc hp
  obtain ⟨delta, hdelta, hnear⟩ := (Metric.continuousAt_iff (a := Jc)).mp
    (Phi.continuous_postcomp (X := AddCircle L)).continuousAt eps heps
  obtain ⟨eta, heta, hthick⟩ := hK.exists_thickening_subset_open hO hKO
  let tol := min (delta / 2) (eta / 2)
  have htol : 0 < tol := lt_min (half_pos hdelta) (half_pos heta)
  have htoldelta : tol < delta := (min_le_left _ _).trans_lt (half_lt_self hdelta)
  have htoleta : tol < eta := (min_le_right _ _).trans_lt (half_lt_self heta)
  obtain ⟨h, hh, hhper, happ⟩ := exists_periodic_smooth_C2_approximation hL hc hp htol
  have hh2 : ContDiff ℝ 2 h := hh.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hhO (x : ℝ) : h x ∈ O := hthick (Metric.mem_thickening_iff.mpr
    ⟨c x, mem_range_self x, by simpa only [dist_eq_norm] using (happ x).1.trans htoleta⟩)
  let Jh := jet h hh2 hhper
  have hnorm : ‖Jh - Jc‖ ≤ tol := by
    apply (ContinuousMap.norm_le _ htol.le).mpr
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ‖jet h hh2 hhper (y : AddCircle L) - jet c hc hp (y : AddCircle L)‖ ≤ tol
    rw [hjet h hh2 hhper y, hjet c hc hp y]
    exact max_le (happ y).1.le (max_le (happ y).2.1.le (happ y).2.2.le)
  have himage : ‖Phi.comp Jh - Phi.comp Jc‖ < eps := by
    have hdist : dist Jh Jc < delta := by
      simpa only [dist_eq_norm] using hnorm.trans_lt htoldelta
    simpa only [dist_eq_norm] using hnear hdist
  let r := fun x => P (h x)
  have hr : ContDiff ℝ ∞ r := contDiff_iff_contDiffAt.mpr (fun x =>
    (hP.contDiffAt (hU.mem_nhds (hOU (hhO x)))).comp x hh.contDiffAt)
  have hGc : G ∘ c = c := funext (fun x => (hGP (hKO (mem_range_self x))).trans (hfix x))
  have hGh : G ∘ h = r := funext (fun x => hGP (hhO x))
  refine ⟨r, hr, hhper.comp P, fun x => ⟨hPU (hOU (hhO x)), hPP _ (hOU (hhO x))⟩, ?_⟩
  intro x
  have hv := ((Phi.comp Jh - Phi.comp Jc).norm_coe_le_norm
    (x : AddCircle L)).trans_lt himage
  change ‖Phi (jet h hh2 hhper (x : AddCircle L)) -
    Phi (jet c hc hp (x : AddCircle L))‖ < eps at hv
  rw [hPhi h hh2 hhper x, hPhi c hc hp x, hGh, hGc] at hv
  exact ⟨(norm_fst_le _).trans_lt hv,
    ((norm_fst_le _).trans (norm_snd_le _)).trans_lt hv,
    ((norm_snd_le _).trans (norm_snd_le _)).trans_lt hv⟩

end PoincareConjecture.M63
