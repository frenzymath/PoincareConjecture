import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Uniqueness.Open
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Uniqueness.Compact
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Plane.CompactModification
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.BoundedExistence
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.TangentTurning
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Topology.Order.Monotone

noncomputable section

open Set Filter Function Metric
open scoped ContDiff Topology

namespace Poincare.ODE.Plane

private theorem contDiff_integralCurve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : E → E} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) : ContDiff ℝ ∞ γ := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hc : ContDiffOn ℝ ∞ γ (Icc (t - 1) (t + 1)) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
      (f := fun _ x => V x) (u := univ)
      (hV.comp contDiff_snd).contDiffOn
      (fun s _ => (hγ s).hasDerivWithinAt) (mapsTo_univ _ _)
  exact hc.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))

private theorem periodic_integralCurve_of_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → E} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) {a b : ℝ}
    (hab : γ a = γ b) : Function.Periodic γ (b - a) := by
  have hs : ∀ t ∈ (univ : Set ℝ),
      γ (t + (b - a)) ∈ (univ : Set E) ∧
        HasDerivAt (fun s => γ (s + (b - a))) (V (γ (t + (b - a)))) t := by
    intro t _
    refine ⟨mem_univ _, ?_⟩
    simpa only [Function.comp_def, one_smul, id_eq] using
      (hγ (t + (b - a))).scomp t ((hasDerivAt_id t).add_const (b - a))
  have heq := Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hV.contDiffOn
    isOpen_univ isPreconnected_univ hs (fun t _ => ⟨mem_univ _, hγ t⟩)
    (a := a) (mem_univ a) (by
      rw [show a + (b - a) = b by ring]
      exact hab.symm)
  exact fun t => heq (mem_univ t)

private theorem exists_least_period_integralCurve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V : E → E} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) (hne : V (γ 0) ≠ 0)
    {q : ℝ} (hq : 0 < q) (hper : Function.Periodic γ q) :
    ∃ P > 0, Function.Periodic γ P ∧
      ∀ s u, 0 < u → u < P → γ (s + u) ≠ γ s := by
  have hγsmooth := contDiff_integralCurve hV hγ
  have hsl : Continuous (fun t => dslope γ 0 t) :=
    (Poincare.Analysis.contDiff_dslope_uncurry hγsmooth).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hsl0 : dslope γ 0 0 ≠ 0 := by
    simpa only [dslope_same, (hγ 0).deriv] using hne
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (hsl.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hsl0))
  have hsep : ∀ u, 0 < u → u < δ → γ u ≠ γ 0 := by
    intro u hu huδ heq
    have hn := hδsub (show u ∈ ball (0 : ℝ) δ by simpa [Real.dist_eq, abs_of_pos hu] using huδ)
    apply hn
    change dslope γ 0 u = 0
    rw [dslope_of_ne γ (ne_of_gt hu), slope, heq, vsub_self, smul_zero]
  have hqret : γ q = γ 0 := by simpa only [zero_add] using hper 0
  have hδq : δ ≤ q := le_of_not_gt (fun h => hsep q hq h hqret)
  let S : Set ℝ := Ici δ ∩ {t | γ t = γ 0}
  have hSclosed : IsClosed S :=
    isClosed_Ici.inter (isClosed_eq hγsmooth.continuous continuous_const)
  have hSne : S.Nonempty := ⟨q, hδq, hqret⟩
  have hSbdd : BddBelow S := ⟨δ, fun _ ht => ht.1⟩
  let P := sInf S
  have hPmem : P ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hP : 0 < P := hδ.trans_le hPmem.1
  have hPper : Function.Periodic γ P := by
    simpa only [sub_zero] using periodic_integralCurve_of_eq hV hγ hPmem.2.symm
  refine ⟨P, hP, hPper, ?_⟩
  intro s u hu huP heq
  have huper : Function.Periodic γ u := by
    simpa only [add_sub_cancel_left] using periodic_integralCurve_of_eq hV hγ heq.symm
  have huret : γ u = γ 0 := by simpa only [zero_add] using huper 0
  have hδu : δ ≤ u := le_of_not_gt (fun h => hsep u hu h huret)
  exact (not_le_of_gt huP) (csInf_le hSbdd (show u ∈ S from ⟨hδu, huret⟩))

theorem injective_integralCurve_of_nonvanishing
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t) : Function.Injective γ := by
  have hno : ∀ a b : ℝ, a < b → γ a ≠ γ b := by
    intro a b hab heq
    obtain ⟨P, hP, hper, hsep⟩ := exists_least_period_integralCurve hV hγ (hne (γ 0))
      (sub_pos.mpr hab) (periodic_integralCurve_of_eq hV hγ heq)
    let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ :=
      Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv
    let f : EuclideanSpace ℝ (Fin 2) → ℂ := fun x => e (V x)
    have hf : ContDiff ℝ ∞ f := e.contDiff.comp hV
    have hfne : ∀ x, f x ≠ 0 := fun x h => hne x (e.injective (h.trans (map_zero e).symm))
    obtain ⟨L, hL, _, hlift⟩ := Poincare.Complex.exists_contDiff_logarithm hf hfne
      0 (Complex.log (f 0)) (Complex.exp_log (hfne 0))
    have hγsmooth := contDiff_integralCurve hV hγ
    apply Poincare.Topology.Plane.not_periodic_tangent_logarithm
      (γ := fun t => e (γ t)) (e.contDiff.comp hγsmooth) hP
      (fun t => congrArg e (hper t))
      (fun s u hu huP he => hsep s u hu huP (e.injective he))
      (L := fun t => L (γ t)) (hL.continuous.comp hγsmooth.continuous)
      (fun t => congrArg L (hper t))
    intro t
    rw [hlift]
    exact (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv.symm
  intro a b heq
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (hno a b hab heq)
  · exact hab
  · exact False.elim (hno b a hab heq.symm)

theorem injOn_integralCurve_Icc_of_nonvanishing
    {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (V (γ t)) t) :
    InjOn γ (Icc a b) := by
  have hc : ContinuousOn γ (Icc a b) :=
    fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  obtain ⟨W, hW, hWne, hWV, S, v, hS, hfix⟩ :=
    exists_nonvanishing_compact_modification hV hne
      (isCompact_Icc.image_of_continuousOn hc)
  obtain ⟨β, hβ0, hβ⟩ :=
    exists_global_solution_of_eq_const_off_compact hW hS hfix (γ a)
  have hβinj := injective_integralCurve_of_nonvanishing hW hWne hβ
  have heq : EqOn γ (fun t => β (t - a)) (Icc a b) := by
    apply eqOn_Icc_of_hasDerivAt (hW.of_le (by simp))
    · intro t ht
      rw [hWV ⟨t, ht, rfl⟩]
      exact hγ t ht
    · intro t _
      simpa only [Function.comp_def, one_smul, id_eq] using
        (hβ (t - a)).scomp t ((hasDerivAt_id t).sub_const a)
    · simpa using hβ0.symm
  intro s hs t ht hst
  have h := hβinj ((heq hs).symm.trans (hst.trans (heq ht)))
  exact sub_left_injective h

end Poincare.ODE.Plane
