import PoincareConjecture.Proofs.M15.Thm8_10_PathProjection
import PoincareConjecture.Proofs.M15.Lemma8_3_Action
import PoincareConjecture.Proofs.M08.PathCongruence










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval}



theorem ordinaryProduct_backwardLAction_congr
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    {T a b : ℝ} {x y : (ordinaryProductTransport F P).Point}
    (p q : M14BackwardPath (ordinaryProductTransport F P) T a b x y)
    (hcurve : EqOn p.curve q.curve (Icc a b)) :
    M14BackwardLAction (ordinaryProductTransport F P) p =
      M14BackwardLAction (ordinaryProductTransport F P) q := by
  have haction (r : M14BackwardPath (ordinaryProductTransport F P) T a b x y) :
      M14BackwardLAction (ordinaryProductTransport F P) r =
        backwardLLength F T a b (fun s => (r.curve s).2) := by
    apply intervalIntegral.integral_congr_Ioo_of_le r.tau_lt.le
    intro s hs
    exact (ordinaryProduct_backwardIntegrand_eq hM12 F P r hs).symm
  rw [haction p, haction q]
  exact M08.backwardLLength_congr F T p.tau_lt.le
    (fun s hs => congrArg Prod.snd (hcurve hs))




theorem ordinaryProduct_stable_reducedLength_eq
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    {T tau : ℝ} {x : (ordinaryProductTransport F P).Point}
    {E : M14ExponentialFamily (ordinaryProductTransport F P) T x}
    (H : M14StableSet (ordinaryProductTransport F P) T tau x E)
    {Z : (ordinaryProductTransport F P).Horizontal x} (hZ : Z ∈ H.carrier) :
    E.reduced_length Z (Real.sqrt tau) =
      M14ReducedLengthValue (ordinaryProductTransport F P) T 0 tau x
        (H.endpoint_map Z) := by
  have ht : Real.sqrt tau ^ 2 = tau := Real.sq_sqrt H.tau_pos.le
  have hpos : 0 < Real.sqrt tau := Real.sqrt_pos.mpr H.tau_pos
  have hs := H.survivor Z hZ
  obtain ⟨p, htrace, hp, _⟩ := H.minimizing_path Z hZ
  have haction : E.action Z (Real.sqrt tau) =
      M14ActionValue (ordinaryProductTransport F P) T 0 tau x (H.endpoint_map Z) := by
    rw [actionValue_eq_of_minimizing p hp]
    have hex : ∃ q : M14BackwardPath (ordinaryProductTransport F P) T 0
        (Real.sqrt tau ^ 2) x (E.gamma Z (Real.sqrt tau)),
        EqOn q.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 (Real.sqrt tau ^ 2)) ∧
        E.action Z (Real.sqrt tau) = M14BackwardLAction (ordinaryProductTransport F P) q :=
      ⟨E.path Z (Real.sqrt tau) hs hpos,
        E.path_coherent Z (Real.sqrt tau) hs hpos,
        E.action_eq Z (Real.sqrt tau) hs hpos⟩
    rw [ht, ← H.endpoint_map_eq Z hZ] at hex
    obtain ⟨hq, hqtrace, hqa⟩ := hex
    exact hqa.trans (ordinaryProduct_backwardLAction_congr hM12 F P hq p
      (fun _ hsmem => (hqtrace hsmem).trans (htrace hsmem).symm))
  rw [E.reduced_length_eq Z (Real.sqrt tau) hs hpos, haction]
  rfl

end PoincareConjecture.Proofs.M15
