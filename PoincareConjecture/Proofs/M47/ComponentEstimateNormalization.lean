import PoincareConjecture.Proofs.M47.ComponentEstimateStrictHistory
import PoincareConjecture.Proofs.M47.ComponentEstimatePinching
import PoincareConjecture.Proofs.M13.ContractionTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem exists_component_normalized_history
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {origin d Q L : ℝ}
    (hd : 0 < d) (hQ : 0 < Q) (hQexp : Real.exp 4 ≤ Q) (hL : 1 ≤ L)
    (U : TopologicalSpace.Opens (F.slice origin).carrier)
    (hne : (U : Set (F.slice origin).carrier).Nonempty)
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc (-d / Q) 0) U)
    (he : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (hscalar : ∀ s : ℝ, ∀ hs : s ∈ Ioc (-d / Q) 0, ∀ x : U,
      (F.connection (origin + s / 1)).scalarCurvature
        (e.forward s ⟨hs.1.le, hs.2⟩ x.val) ≤ L * Q)
    (hpinch : ∀ t ∈ Icc (origin - d / Q) origin, SurgeryPinchedAt (F.connection t) t) :
    ∃ G : RicciFlow 3 U (Icc 0 (d / 2)),
      (∀ t ∈ Icc 0 (d / 2), ∀ x : U, (G.connection t).curvatureTensorNorm x ≤ 13 * L) ∧
      ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
        (G.metric (d / 2)).inner x v w = Q * (F.metric origin).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) x w) := by
  have ha : -d / Q < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hd) hQ
  obtain ⟨G0, hread⟩ := exists_component_strict_ordinary_history P ha U hne e
  have hterminal (x : U) (v w : TangentSpace (𝓡 3) x) :
      (G0.metric origin).inner x v w = (F.metric origin).inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) x w) := by
    have hfunctions :
        (⟨origin + 0 / 1, fun y : U => e.forward 0 ⟨ha.le, le_rfl⟩ y.val⟩ :
          (t : ℝ) × (U → (F.slice t).carrier)) =
            ⟨origin, (Subtype.val : U → (F.slice origin).carrier)⟩ := by
      apply Sigma.ext (by simp)
      apply Function.hfunext rfl
      intro y y' hyy
      cases hyy
      exact he _ y.val y.property
    have hpull := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.metric p.1).inner (p.2 x)
        (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
    exact (congrArg (fun t => (G0.metric t).inner x v w)
      (show origin + 0 / 1 = origin by simp)).symm.trans
        ((((hread 0 ⟨ha, le_rfl⟩ x).1 v w).symm).trans hpull)
  let T := d / 2
  let start := origin - T / Q
  have hT : 0 < T := half_pos hd
  have hhalf : T / Q = (d / Q) / 2 := by dsimp only [T]; ring
  have hstart : origin + (-d / Q) < start := by
    dsimp only [start]
    rw [hhalf, neg_div]
    linarith [div_pos hd hQ]
  have hstartEnd : start < origin := by dsimp only [start]; linarith [div_pos hT hQ]
  have hsub : Icc start origin ⊆ Ioc (origin + (-d / Q)) origin := by
    intro t ht
    exact ⟨hstart.trans_le ht.1, ht.2⟩
  let I : SpacetimeInterval := {
    domain := Icc start origin
    ordConnected := ordConnected_Icc
    nontrivial := ⟨start, ⟨le_rfl, hstartEnd.le⟩,
      origin, ⟨hstartEnd.le, le_rfl⟩, hstartEnd.ne⟩
  }
  let G1 : RicciFlow 3 U I.domain := {
    metric := G0.metric
    connection := G0.connection
    interval := ordConnected_Icc
    nontrivial := I.nontrivial
    smooth := G0.smooth.mono (Set.prod_mono hsub Subset.rfl)
    equation := fun t ht x v w => (G0.equation t (hsub ht) x v w).mono hsub
  }
  obtain ⟨R⟩ := P.m13.ordinary_flow U I G1 Q hQ start
  have hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      parabolicTimeInv Q start s ∈ I.domain := by
    change start + s / Q ∈ Icc start origin
    have hsQ : s / Q ≤ T / Q := div_le_div_of_nonneg_right hs.2 hQ.le
    constructor
    · linarith [div_nonneg hs.1 hQ.le]
    · dsimp only [start]
      linarith
  have hnormalized : Icc (0 : ℝ) T ⊆ (parabolicInterval Q hQ start I).domain := by
    intro s hs
    exact (mem_parabolicInterval_iff Q hQ start I s).2 (hclock s hs)
  let G : RicciFlow 3 U (Icc 0 T) := {
    metric := R.flow.metric
    connection := R.flow.connection
    interval := ordConnected_Icc
    nontrivial := ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩
    smooth := R.flow.smooth.mono (Set.prod_mono hnormalized Subset.rfl)
    equation := fun t ht x v w => (R.flow.equation t (hnormalized ht) x v w).mono hnormalized
  }
  refine ⟨G, ?_, ?_⟩
  · intro s hs x
    have hnorm : (G.connection s).curvatureTensorNorm x =
        (G1.connection (parabolicTimeInv Q start s)).curvatureTensorNorm x / Q := by
      simpa only [Diffeomorph.coe_refl, id_eq] using
        M13.homothety_curvatureTensorNorm_eq _ _ (Diffeomorph.refl (𝓡 3) U ∞)
          Q hQ (R.metric_homothety s) (G1.connection _) (R.flow.connection s) x
    rw [hnorm]
    apply (div_le_iff₀ hQ).2
    let t := parabolicTimeInv Q start s
    have ht : t ∈ Ioc (origin + (-d / Q)) origin := hsub (hclock s hs)
    have hparam : t - origin ∈ Ioc (-d / Q) 0 := by
      constructor <;> linarith [ht.1, ht.2]
    have hc : origin + (t - origin) / 1 = t := by simp only [div_one, add_sub_cancel]
    have hnormRead : (G0.connection t).curvatureTensorNorm x =
        (F.connection (origin + (t - origin) / 1)).curvatureTensorNorm
          (e.forward (t - origin) ⟨hparam.1.le, hparam.2⟩ x.val) :=
      (congrArg (fun r => (G0.connection r).curvatureTensorNorm x) hc).symm.trans
        (hread (t - origin) hparam x).2.2
    have hwindow : origin + (t - origin) / 1 ∈ Icc (origin - d / Q) origin := by
      rw [hc]
      constructor
      · simpa only [neg_div, sub_eq_add_neg] using ht.1.le
      · exact ht.2
    have hbound := component_pinched_curvature_bound P (hpinch _ hwindow) hQexp hL
      (mem_univ _) (hscalar (t - origin) hparam x)
    change (G0.connection t).curvatureTensorNorm x ≤ _
    rw [hnormRead]
    nlinarith [hbound]
  · intro x v w
    have hend : parabolicTimeInv Q start T = origin := by
      dsimp only [parabolicTimeInv, start]
      ring
    have hm := R.metric_eq T x v w
    rw [hend] at hm
    exact hm.trans (congrArg (fun r : ℝ => Q * r) (hterminal x v w))

end PoincareConjecture.M47
