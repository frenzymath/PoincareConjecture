import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Initial.InitialComparison
import PoincareLib.Geometry.Riemannian.Coordinates.Transitions

/-!
# The initial comparison chart on the actual surgery slice

Morgan--Tian, Claim 16.6 and Corollary 16.7, pp. 371-372. An actual
M36 local-result comparison yields the initial chart and inverse on the
post-surgery carrier. Extending the chart by its tip keeps its entire
range in the region where the inverse is smooth. Exact metric-ball
image equality is a separate geometric obligation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

/-- An M36 witness supplies the actual initial chart and its local metric
link in Proposition 16.5, p. 370. The conclusion does not assert exact
image equality with the physical metric ball. -/
theorem initial_cap_chart_of_comparison
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {A eta : ℝ} (hA : 0 < A) (hAeta : A ≤ eta⁻¹)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output
      ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip
      (((F.event t hT).necks i).neck.scale) eta)
    (hdelta : ((F.event t hT).necks i).neck.epsilon ≤
      F.local_constants.comparison_delta eta) :
    ∃ initial : SurgeryCapInitialComparison F t hT i A,
      initial.chart '' F.standard_initial.metric.ball 0 A =
        (fun x => (F.event t hT).local_embed i (Q.map x)) ''
          F.standard_initial.metric.ball 0 A := by
  classical
  let E := F.event t hT
  let L := E.local_embed i
  let B := F.standard_initial.metric.ball 0 A
  let f : StandardCapSpace → (F.slice t).carrier := fun x => L (Q.map x)
  let chart : StandardCapSpace → (F.slice t).carrier :=
    fun x => if x ∈ B then f x else f 0
  let : Nonempty (E.local_result i).output.carrier := ⟨(E.local_result i).tip⟩
  let inverse : (F.slice t).carrier → StandardCapSpace :=
    fun y => Q.inverse (Function.invFun L y)
  have hzero : (0 : StandardCapSpace) ∈ B := by
    change F.standard_initial.metric.edist 0 0 < ENNReal.ofReal A
    have hself : F.standard_initial.metric.edist 0 0 = 0 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
        ⟨F.standard_initial.metric.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_self
    rw [hself]
    exact ENNReal.ofReal_pos.mpr hA
  have hsub : B ⊆ F.standard_initial.metric.ball 0 eta⁻¹ :=
    fun _ hx => lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hAeta)
  have hchart (x : StandardCapSpace) (hx : x ∈ B) : chart x = f x := if_pos hx
  have hrange : range chart = f '' B := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : x ∈ B
      · exact ⟨x, hx, (hchart x hx).symm⟩
      · exact ⟨0, hzero, (if_neg hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hchart x hx⟩
  have hLi : Function.LeftInverse (Function.invFun L) L :=
    Function.leftInverse_invFun (E.local_embed_injective i)
  have hLsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Function.invFun L) (range L) :=
    (E.local_result i).metric.contMDiffOn_invFun_of_injective_pullback_eq
      (F.metric t) (E.local_embed_smooth i) (E.local_embed_injective i) (E.local_metric i)
  have hLrange : f '' B ⊆ range L := by
    rintro _ ⟨x, _, rfl⟩
    exact ⟨Q.map x, rfl⟩
  have hmaps : MapsTo (Function.invFun L) (f '' B)
      (Q.map '' F.standard_initial.metric.ball 0 eta⁻¹) := by
    rintro _ ⟨x, hx, rfl⟩
    change Function.invFun L (L (Q.map x)) ∈ _
    rw [hLi]
    exact mem_image_of_mem Q.map (hsub hx)
  have hinverse : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse (range chart) := by
    rw [hrange]
    exact Q.inverse_smooth.comp (hLsmooth.mono hLrange) hmaps
  have hleft : LeftInvOn inverse chart B := by
    intro x hx
    rw [hchart x hx]
    change Q.inverse (Function.invFun L (L (Q.map x))) = x
    rw [hLi]
    exact Q.left_inverse (hsub hx)
  have hright : LeftInvOn chart inverse (range chart) := by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ B
    · rw [hleft hx]
    · have hc : chart x = chart 0 := (if_neg hx).trans (hchart 0 hzero).symm
      rw [hc, hleft hzero]
  refine ⟨{
    A_pos := hA
    chart := chart
    inverse := inverse
    chart_smooth := ((E.local_embed_smooth i).comp_contMDiffOn
      (Q.map_smooth.mono hsub)).congr hchart
    inverse_smooth := hinverse
    left_inverse := hleft
    right_inverse := hright
    tip_eq := ?_
    local_metric_link := ?_
  }, ?_⟩
  · rw [hchart 0 hzero]
    exact (congrArg L Q.map_tip).trans (E.local_tip i)
  · refine ⟨eta, Q.eta_pos, Q, hdelta, ?_, hchart⟩
    intro x hx
    exact lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (by linarith : A ≤ eta⁻¹ + 1))
  · exact Set.image_congr hchart

end PoincareMT
