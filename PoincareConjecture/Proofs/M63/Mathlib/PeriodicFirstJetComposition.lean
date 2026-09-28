import PoincareConjecture.Proofs.M63.Mathlib.PeriodicRetractionApproximation
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M63

theorem exists_periodic_C2_tolerance_for_firstJet_composition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {O : Set (E × E)} (hO : IsOpen O) {f : E × E → ℝ}
    (hf : ContDiffOn ℝ 1 f O) {L : ℝ} (hL : 0 < L)
    {c : ℝ → E} (hc : ContDiff ℝ 2 c) (hp : Function.Periodic c L)
    (hcO : ∀ x, (c x, deriv c x) ∈ O) {eps : ℝ} (heps : 0 < eps) :
    ∃ δ > 0, ∀ r : ℝ → E, ContDiff ℝ 2 r → Function.Periodic r L →
      (∀ x, ‖r x - c x‖ < δ ∧ ‖deriv r x - deriv c x‖ < δ ∧
        ‖deriv (deriv r) x - deriv (deriv c) x‖ < δ) →
      (∀ x, (r x, deriv r x) ∈ O) ∧
      ContDiff ℝ 1 (fun x => f (r x, deriv r x)) ∧
      ∀ x, |f (r x, deriv r x) - f (c x, deriv c x)| < eps ∧
        |deriv (fun y => f (r y, deriv r y)) x -
          deriv (fun y => f (c y, deriv c y)) x| < eps := by
  let : Fact (0 < L) := ⟨hL⟩
  let J := fun x => (c x, deriv c x)
  have hc1 : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hp1 := hp.deriv_of_differentiable (hc.differentiable (by norm_num))
  have hJper : Function.Periodic J L := by
    intro x
    dsimp only [J]
    rw [hp x, hp1 x]
  have hJ : ContDiff ℝ 1 J := (hc.of_le (by norm_num)).prodMk hc1
  have hK : IsCompact (range J) := hJper.compact_of_continuous hL.ne' hJ.continuous
  obtain ⟨G, hG, _hGc, V, hV, hKV, hVO, hGf⟩ :=
    exists_finiteOrder_compact_extension 1 hK hO (by rintro _ ⟨x, rfl⟩; exact hcO x) f hf
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  let Phi : C(E × E × E, ℝ × ℝ) :=
    ⟨fun z => (G (z.1, z.2.1), fderiv ℝ G (z.1, z.2.1) (z.2.1, z.2.2)),
      (G.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        ((hDG.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).clm_apply
          ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))⟩
  let jet (d : ℝ → E) (hd : ContDiff ℝ 2 d) (hdp : Function.Periodic d L) :
      C(AddCircle L, E × E × E) := by
    have hd1 : ContDiff ℝ 1 (deriv d) := hd.deriv' (n := 1)
    have hp1 := hdp.deriv_of_differentiable (hd.differentiable (by norm_num))
    have hp2 := hp1.deriv_of_differentiable (hd1.differentiable (by norm_num))
    let K := fun x => (d x, deriv d x, deriv (deriv d) x)
    have hK : Function.Periodic K L := by
      intro x
      dsimp only [K]
      rw [hdp x, hp1 x, hp2 x]
    exact ⟨hK.lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
        (hd.continuous.prodMk (hd1.continuous.prodMk hd1.continuous_deriv_one))⟩
  have hjet (d : ℝ → E) (hd : ContDiff ℝ 2 d) (hdp : Function.Periodic d L) (x : ℝ) :
      jet d hd hdp (x : AddCircle L) = (d x, deriv d x, deriv (deriv d) x) := rfl
  have hPhi (d : ℝ → E) (hd : ContDiff ℝ 2 d) (hdp : Function.Periodic d L) (x : ℝ) :
      Phi (jet d hd hdp (x : AddCircle L)) =
        (G (d x, deriv d x), deriv (fun y => G (d y, deriv d y)) x) := by
    have hd1 : ContDiff ℝ 1 (deriv d) := hd.deriv' (n := 1)
    have hcomp := ((hG.differentiable (by norm_num) (d x, deriv d x)).hasFDerivAt).comp_hasDerivAt
      x (((hd.differentiable (by norm_num) x).hasDerivAt).prodMk
        (hd1.differentiable (by norm_num) x).hasDerivAt)
    change (G (d x, deriv d x), fderiv ℝ G (d x, deriv d x)
      (deriv d x, deriv (deriv d) x)) = _
    exact Prod.ext rfl hcomp.deriv.symm
  let Jc := jet c hc hp
  obtain ⟨eta, heta, hnear⟩ := (Metric.continuousAt_iff (a := Jc)).mp
    (Phi.continuous_postcomp (X := AddCircle L)).continuousAt eps heps
  obtain ⟨rho, hrho, hthick⟩ := hK.exists_thickening_subset_open hV hKV
  let δ := min (eta / 2) (rho / 2)
  have hδ : 0 < δ := lt_min (half_pos heta) (half_pos hrho)
  have hδη : δ < eta := (min_le_left _ _).trans_lt (half_lt_self heta)
  have hδrho : δ < rho := (min_le_right _ _).trans_lt (half_lt_self hrho)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrp happ
  have hrV (x : ℝ) : (r x, deriv r x) ∈ V := by
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    refine ⟨J x, mem_range_self x, ?_⟩
    change dist (r x, deriv r x) (c x, deriv c x) < rho
    rw [dist_eq_norm]
    exact (max_le (happ x).1.le (happ x).2.1.le).trans_lt hδrho
  have hGr : (fun x => G (r x, deriv r x)) = fun x => f (r x, deriv r x) :=
    funext fun x => hGf (hrV x)
  have hGc : (fun x => G (c x, deriv c x)) = fun x => f (c x, deriv c x) :=
    funext fun x => hGf (hKV (mem_range_self x))
  have hreg : ContDiff ℝ 1 (fun x => f (r x, deriv r x)) := by
    rw [← hGr]
    exact hG.comp ((hr.of_le (by norm_num)).prodMk (hr.deriv' (n := 1)))
  let Jr := jet r hr hrp
  have hnorm : ‖Jr - Jc‖ ≤ δ := by
    apply (ContinuousMap.norm_le _ hδ.le).mpr
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    change ‖jet r hr hrp (y : AddCircle L) - jet c hc hp (y : AddCircle L)‖ ≤ δ
    rw [hjet r hr hrp y, hjet c hc hp y]
    exact max_le (happ y).1.le (max_le (happ y).2.1.le (happ y).2.2.le)
  have himage : ‖Phi.comp Jr - Phi.comp Jc‖ < eps := by
    have hdist : dist Jr Jc < eta := by simpa only [dist_eq_norm] using hnorm.trans_lt hδη
    simpa only [dist_eq_norm] using hnear hdist
  refine ⟨fun x => hVO (hrV x), hreg, ?_⟩
  intro x
  have hval := ((Phi.comp Jr - Phi.comp Jc).norm_coe_le_norm
    (x : AddCircle L)).trans_lt himage
  change ‖Phi (jet r hr hrp (x : AddCircle L)) -
    Phi (jet c hc hp (x : AddCircle L))‖ < eps at hval
  rw [hPhi r hr hrp x, hPhi c hc hp x] at hval
  have hrval := congrFun hGr x
  have hcval := congrFun hGc x
  rw [hrval, hcval, hGr, hGc] at hval
  exact ⟨(norm_fst_le _).trans_lt hval, (norm_snd_le _).trans_lt hval⟩

end PoincareConjecture.M63
