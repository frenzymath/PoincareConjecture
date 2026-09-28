import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarComplexHarmonic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric InnerProductSpace
open scoped Topology

namespace PoincareConjecture

theorem m64ComplexHarmonicAt_eventually_eq_of_isLocalMin
    {f : ℂ → ℝ} {z : ℂ} (hf : HarmonicAt f z) (hmin : IsLocalMin f z) :
    f =ᶠ[𝓝 z] fun _ => f z := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hf.eventually
  obtain ⟨H, hH, hre⟩ :=
    HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (show HarmonicOnNhd f (ball z r) from hball)
  let G := fun w => Complex.exp (-H w)
  have hnorm : (fun w => ‖G w‖) =ᶠ[𝓝 z] fun w => Real.exp (-f w) := by
    filter_upwards [ball_mem_nhds z hr] with w hw
    simp only [G, Complex.norm_exp, Complex.neg_re, hre hw]
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w := by
    filter_upwards [ball_mem_nhds z hr] with w hw
    exact ((hH w hw).differentiableAt.neg).cexp
  have hmax : IsLocalMax (norm ∘ G) z := by
    change ∀ᶠ w in 𝓝 z, ‖G w‖ ≤ ‖G z‖
    filter_upwards [hmin, hnorm] with w hw hn
    rw [hn, hnorm.eq_of_nhds]
    exact Real.exp_le_exp.mpr (neg_le_neg hw)
  have hconstant := Complex.norm_eventually_eq_of_isLocalMax hdiff hmax
  filter_upwards [hconstant, hnorm] with w hw hn
  have he : Real.exp (-f w) = Real.exp (-f z) := hn.symm.trans (hw.trans hnorm.eq_of_nhds)
  exact neg_injective (Real.exp_injective he)

theorem m64PlaneHarmonicAt_eventually_eq_of_isLocalMin
    {f : LoopPlane → ℝ} {p : LoopPlane} (hf : HarmonicAt f p) (hmin : IsLocalMin f p) :
    f =ᶠ[𝓝 p] fun _ => f p := by
  let e := Complex.orthonormalBasisOneI.repr
  let z := e.symm p
  have hez : e z = p := e.apply_symm_apply p
  have hh : HarmonicAt (f ∘ e) z :=
    M64Uniformization.scalar_harmonicAt_complex_coordinates (hez.symm ▸ hf)
  have hm : IsLocalMin (f ∘ e) z := by
    have h := (e.continuous.continuousAt.tendsto).eventually (hez.symm ▸ hmin)
    exact h
  have hlocal := m64ComplexHarmonicAt_eventually_eq_of_isLocalMin hh hm
  have hback := (e.symm.continuous.continuousAt.tendsto).eventually hlocal
  change ∀ᶠ x in 𝓝 p, f x = f p
  simpa only [Function.comp_apply, hez, e.apply_symm_apply] using hback

theorem m64PlaneHarmonicOnNhd_eqOn_of_minimum
    {f : LoopPlane → ℝ} {U : Set LoopPlane} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hf : HarmonicOnNhd f U) {p : LoopPlane}
    (hp : p ∈ U) (hmin : ∀ q ∈ U, f p ≤ f q) :
    EqOn f (fun _ => f p) U := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  have hc : Continuous (fun q : U => f q) :=
    continuousOn_iff_continuous_domRestrict.mp hf.continuousOn
  have hclosed : IsClosed {q : U | f q = f p} := isClosed_eq hc continuous_const
  have hopen : IsOpen {q : U | f q = f p} := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hm : IsLocalMin f q := by
      filter_upwards [hU.mem_nhds q.property] with r hr
      exact hq.symm ▸ hmin r hr
    have heq := m64PlaneHarmonicAt_eventually_eq_of_isLocalMin (hf q q.property) hm
    have hback := continuous_subtype_val.continuousAt.tendsto.eventually heq
    filter_upwards [hback] with r hr
    exact hr.trans hq
  have hall := (show IsClopen {q : U | f q = f p} from ⟨hclosed, hopen⟩).eq_univ
    (show ({q : U | f q = f p} : Set U).Nonempty from ⟨⟨p, hp⟩, rfl⟩)
  intro q hq
  exact (Set.eq_univ_iff_forall.mp hall) ⟨q, hq⟩

theorem m64PlaneHarmonicOnNhd_pos_of_nonneg
    {f : LoopPlane → ℝ} {U : Set LoopPlane} (hU : IsOpen U)
    (hconn : IsPreconnected U) (hf : HarmonicOnNhd f U)
    (hnonneg : ∀ p ∈ U, 0 ≤ f p) (hpos : ∃ p ∈ U, 0 < f p) :
    ∀ p ∈ U, 0 < f p := by
  intro p hp
  by_contra h
  have hzero : f p = 0 := le_antisymm (not_lt.mp h) (hnonneg p hp)
  have hconstant := m64PlaneHarmonicOnNhd_eqOn_of_minimum hU hconn hf hp
    (fun q hq => hzero.symm ▸ hnonneg q hq)
  obtain ⟨q, hq, hqp⟩ := hpos
  rw [hconstant hq, hzero] at hqp
  exact lt_irrefl (0 : ℝ) hqp

end PoincareConjecture
