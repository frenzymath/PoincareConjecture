import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.LiftedFamilies.PathComparison
import PoincareConjecture.Proofs.M59.Mathlib.LoopComparisonTransport

set_option autoImplicit false

open scoped Topology unitInterval

namespace IsCoveringMap

open PoincareConjecture PoincareConjecture.Proofs.M02 PoincareConjecture.Proofs.M59

variable {E X S : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S]
  [SimplyConnectedSpace E] {p : E → X}

theorem homotopic_circle_families_of_deck_transport
    (hp : IsCoveringMap p) (q : CubeBoundaryQuotient (Fin 1) S) (c : E)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 E c))
    (hdeck : ∀ (c' : E), p c' = p c → ∀ r : Path c c',
      ∃ (d : C(E, E)) (hd : d c = c'),
        (∀ e, p (d e) = p e) ∧
          ∀ A : HomotopyGroup.Pi 2 C(S, E) (ContinuousMap.const S c),
            homotopyGroupMap (Fin 2) (postcomposeMap S d)
              (postcomposeMap_const S d hd) A =
              (m59HigherBasepointTransport C(S, E) 2).map
                (r.map ContinuousMap.continuous_const') A)
    {a b : GenLoop (Fin 2) C(S, X) (ContinuousMap.const S (p c))}
    {l : Path (ContinuousMap.const S (p c)) (ContinuousMap.const S (p c))}
    (H : GenLoop.HomotopyAlong l a b) : GenLoop.Homotopic a b := by
  obtain ⟨A, hA⟩ := hp.exists_circle_family_lift q c a
  obtain ⟨c', hc', B, L, ⟨K⟩, hB, _⟩ := hp.exists_circle_homotopyAlong_lift q c H A hA
  let r := PathConnectedSpace.somePath c c'
  obtain ⟨K'⟩ := q.continuousLoop_homotopyAlong_constant hpi K r
  obtain ⟨d, hd, hdp, hdclass⟩ := hdeck c' hc' r
  let D := mapGenLoop (postcomposeMap S d) (postcomposeMap_const S d hd) A
  have hDB : GenLoop.Homotopic D B := by
    have heq : (⟦D⟧ : HomotopyGroup.Pi 2 C(S, E) (ContinuousMap.const S c')) = ⟦B⟧ :=
      (hdclass ⟦A⟧).trans
      (Quotient.sound (GenLoop.boundaryTransport_homotopic_of_homotopyAlong K'))
    exact Quotient.exact heq
  have hD : mapGenLoop (postcomposeMap S ⟨p, hp.continuous⟩)
      (postcomposeMap_const S ⟨p, hp.continuous⟩ hc') D = a := by
    ext v s
    exact (hdp (A v s)).trans
      (congrArg (fun g : GenLoop (Fin 2) C(S, X) (ContinuousMap.const S (p c)) =>
        g v s) hA)
  have h := mapGenLoop_homotopic (postcomposeMap S ⟨p, hp.continuous⟩)
    (postcomposeMap_const S ⟨p, hp.continuous⟩ hc') hDB
  rwa [hD, hB] at h

theorem homotopic_circle_families_of_deck_piThree
    (hp : IsCoveringMap p) (q : CubeBoundaryQuotient (Fin 1) S) (c : E)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 E c))
    (hdeck : ∀ (c' : E), p c' = p c → ∀ r : Path c c',
      ∃ (d : C(E, E)) (hd : d c = c'),
        (∀ e, p (d e) = p e) ∧
          ∀ A : HomotopyGroup.Pi 3 E c,
            homotopyGroupMap (Fin 3) d hd A =
              (m59HigherBasepointTransport E 3).map r A)
    {a b : GenLoop (Fin 2) C(S, X) (ContinuousMap.const S (p c))}
    {l : Path (ContinuousMap.const S (p c)) (ContinuousMap.const S (p c))}
    (H : GenLoop.HomotopyAlong l a b) : GenLoop.Homotopic a b := by
  apply hp.homotopic_circle_families_of_deck_transport q c hpi ?_ H
  intro c' hc' r
  obtain ⟨d, hd, hdp, hdclass⟩ := hdeck c' hc' r
  let T := m59HigherBasepointTransport E 2
  have hpi' : Subsingleton (HomotopyGroup.Pi 2 E c') := by
    constructor
    intro a b
    have ha : T.map r (T.map r.symm a) = a := by
      simpa using T.map_left_inverse r.symm a
    have hb : T.map r (T.map r.symm b) = b := by
      simpa using T.map_left_inverse r.symm b
    exact ha.symm.trans ((congrArg (T.map r) (hpi.elim _ _)).trans hb)
  refine ⟨d, hd, hdp, ?_⟩
  intro A
  apply (q.loopHomotopyEquiv 2 c' hpi').injective
  refine (q.loopHomotopyEquiv_naturality 2 hpi hpi' d hd A).trans
    ((hdclass _).trans ?_)
  refine Quotient.inductionOn A fun a => ?_
  exact q.loopHomotopyEquiv_homotopyAlong 2 hpi hpi' r
    (GenLoop.boundaryTransportHomotopy (constantMapPath (S := S) r) a)

end IsCoveringMap
