import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePieceRecovery
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeWeakMinimum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem actionValue_le_gauge_pieces (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (u : ∀ i, ℝ → G.gaugeCover.spatial (R.gauge i).index)
    (hu : ∀ i, ContinuousOn (u i) (Icc (R.node i.castSucc) (R.node i.succ)))
    (hleft : ∀ i, u i (R.node i.castSucc) = ((R.gauge i).lift (gamma (R.node i.castSucc))).2)
    (hright : ∀ i, u i (R.node i.succ) = ((R.gauge i).lift (gamma (R.node i.succ))).2)
    (w : ∀ i, M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (R.node i.castSucc) (R.node i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (R.node i.castSucc) (R.node i.succ) →
      (u i s).val = (u i (R.node i.castSucc)).val + ∫ r in R.node i.castSucc..s, w i r) :
    M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau)) ≤
      ∑ i, gaugeCylinderAction (R.gauge i).index
        (fun s => ((R.gauge i).lift (gamma s)).1) (u i) (w i) := by
  obtain ⟨p, hp⟩ := gauge_piece_recovery_sequence hM12 htau gamma hgamma hclock R
    u hu hleft hright w hprimitive
  exact ge_of_tendsto hp (Eventually.of_forall (fun k => M14.actionValue_le_action hfinite (p k)))

theorem gauge_piece_minimum (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hmin : R.action ≤ M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (j : Fin R.count) (u : ℝ → G.gaugeCover.spatial (R.gauge j).index)
    (hu : ContinuousOn u (Icc (R.node j.castSucc) (R.node j.succ)))
    (hleft : u (R.node j.castSucc) = ((R.gauge j).lift (gamma (R.node j.castSucc))).2)
    (hright : u (R.node j.succ) = ((R.gauge j).lift (gamma (R.node j.succ))).2)
    (w : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (R.node j.castSucc) (R.node j.succ))
    (hprimitive : ∀ s ∈ Icc (R.node j.castSucc) (R.node j.succ),
      (u s).val = (u (R.node j.castSucc)).val + ∫ r in R.node j.castSucc..s, w r) :
    gaugeCylinderAction (R.gauge j).index (fun s => ((R.gauge j).lift (gamma s)).1)
        (fun s => ((R.gauge j).lift (gamma s)).2) (R.velocity j) ≤
      gaugeCylinderAction (R.gauge j).index (fun s => ((R.gauge j).lift (gamma s)).1) u w := by
  classical
  let base (i : Fin R.count) (s : ℝ) := ((R.gauge i).lift (gamma s)).2
  let theta (i : Fin R.count) (s : ℝ) := ((R.gauge i).lift (gamma s)).1
  have hsrc (i : Fin R.count) :
      MapsTo gamma (Icc (R.node i.castSucc) (R.node i.succ)) (R.gauge i).source :=
    fun _ hs => R.source i (R.core_subset i hs)
  have hbase (i : Fin R.count) : ContinuousOn (base i)
      (Icc (R.node i.castSucc) (R.node i.succ)) :=
    (R.gauge i).smooth.continuousOn.snd.comp hgamma.continuousOn (hsrc i)
  have hcomp := actionValue_le_gauge_pieces hM12 htau gamma hgamma hclock R hfinite
    (Function.update base j u)
    (by
      intro i
      by_cases h : i = j
      · subst i
        simpa using hu
      · simpa [h] using hbase i)
    (by
      intro i
      by_cases h : i = j
      · subst i
        simpa using hleft
      · simp [h, base])
    (by
      intro i
      by_cases h : i = j
      · subst i
        simpa using hright
      · simp [h, base])
    (Function.update R.velocity j w)
    (by
      intro i
      by_cases h : i = j
      · subst i
        simpa using hprimitive
      · simpa [h, base] using R.primitive i)
  let f (i : Fin R.count) :=
    gaugeCylinderAction (R.gauge i).index (theta i) (base i) (R.velocity i)
  let g (i : Fin R.count) := gaugeCylinderAction (R.gauge i).index (theta i)
    (Function.update base j u i) (Function.update R.velocity j w i)
  have hsum : R.action = ∑ i, f i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (gaugeCylinderAction_eq (R.gauge i) gamma (hsrc i)
      (R.monotone (Fin.castSucc_le_succ i)) (R.velocity i)).symm
  have hle : (∑ i, f i) ≤ ∑ i, g i := by
    rw [← hsum]
    exact hmin.trans hcomp
  have hrest : ∑ i ∈ Finset.univ.erase j, f i = ∑ i ∈ Finset.univ.erase j, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase] at hi
    simp [g, f, hi.1]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j), hrest] at hle
  have := (add_le_add_iff_left _).mp hle
  simpa only [f, g, Function.update_self, theta, base] using this

end PoincareConjecture.Proofs.M46
