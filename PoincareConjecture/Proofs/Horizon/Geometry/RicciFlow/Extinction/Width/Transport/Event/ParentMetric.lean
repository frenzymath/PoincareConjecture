import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Parent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem m67EventPreToParent_metric
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
    (H : RepairedAncestryTransportInput D W P K C)
    (S : Set.Icc (0 : ℝ) T) (hS : S.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice S.1).carrier)
    (s : Set.Icc (0 : ℝ) T)
    (hs : (D.flow.event S.1 hS).tMinus < s.1) (hsS : s.1 < S.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event S.1 hS).tMinus s.1))
    {q : M59SphereQuotient} (pre : M67WidthSlice q (P.component s))
    (hambient : pre.ambient_metric = D.flow.metric s.1)
    (x v w) :
    ((H.event_input S hS hpost).parent_metric s.1).inner
      (m67EventPreToParent H S hS hpost s hs hJ x)
      (mfderiv (𝓡 3) (𝓡 3) (m67EventPreToParent H S hS hpost s hs hJ) x v)
      (mfderiv (𝓡 3) (𝓡 3) (m67EventPreToParent H S hS hpost s hs hJ) x w) =
      pre.metric.inner x v w := by
  let I := H.event_input S hS hpost
  let E := D.flow.event S.1 hS
  let t : Set.Ico E.tMinus S.1 := ⟨s.1, hs.le, hsS⟩
  let e := m67EventPreToParent H S hS hpost s hs hJ
  have hmap : ((E.pre_identify t) ∘ I.parent.inclusion) ∘ e =
      (P.component s).inclusion := by
    funext y
    exact m67EventPreToParent_ambient H S hS hpost s hs hsS hJ y
  have hd (u : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (E.pre_identify t) (I.parent.inclusion (e x))
        (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x u)) =
        mfderiv (𝓡 3) (𝓡 3) (P.component s).inclusion x u := by
    have hh := congrArg (fun f => mfderiv (𝓡 3) (𝓡 3) f x u) hmap
    rw [mfderiv_comp x
      (((E.pre_identify t).contMDiff.comp I.parent.inclusion_smooth).mdifferentiable
        (by simp) (e x)) (e.contMDiff.mdifferentiable (by simp) x),
      mfderiv_comp (e x) ((E.pre_identify t).contMDiff.mdifferentiable (by simp) _)
        (I.parent.inclusion_smooth.mdifferentiable (by simp) _)] at hh
    exact hh
  change (I.parent_metric s.1).inner (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) = _
  rw [← I.parent_pullback t]
  rw [← E.pre_metric t]
  change (D.flow.metric s.1).inner
    (E.pre_identify t (I.parent.inclusion (e x)))
    (mfderiv (𝓡 3) (𝓡 3) (E.pre_identify t) (I.parent.inclusion (e x))
      (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)))
    (mfderiv (𝓡 3) (𝓡 3) (E.pre_identify t) (I.parent.inclusion (e x))
      (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion (e x) (mfderiv (𝓡 3) (𝓡 3) e x w))) = _
  rw [hd v, hd w]
  have hpoint := congrFun hmap x
  change E.pre_identify t (I.parent.inclusion (e x)) = (P.component s).inclusion x at hpoint
  rw [hpoint, ← hambient]
  exact pre.metric_pullback x v w

end PoincareConjecture
