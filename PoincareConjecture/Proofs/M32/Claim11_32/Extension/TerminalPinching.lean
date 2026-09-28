import PoincareConjecture.Proofs.M32.Claim11_32.Extension.LocalIsometry
import PoincareConjecture.Proofs.M32.Claim11_32.Extension.SectionalContinuity
import PoincareConjecture.Proofs.M32.Claim11_32.RegularTimes
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]



theorem terminal_box_eventually
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hT : T ∈ (E.extended.box b).interval) :
    ∀ᶠ t in 𝓝[<] T, t ∈ F.interval ∧ t ∈ (E.extended.box b).interval := by
  obtain ⟨U, hU, heq⟩ := (E.extended.box b).relatively_open
  have hTU : T ∈ U := (heq ▸ hT).2
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (terminalTime_pos H)),
    nhdsWithin_le_nhds (hU.mem_nhds hTU)] with t ht ht0 htU
  have htF : t ∈ F.interval := H.interval_exhausts_preterminal ⟨ht0.le, ht⟩
  exact ⟨htF, heq ▸ ⟨E.old_times htF, htU⟩⟩



theorem box_scalar_pullback (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval)
    (x : (G.box b).carrier.carrier) :
    (G.connection t).scalarCurvature ((G.box b).forward t ht x) =
      ((G.box b).flow.connection t).scalarCurvature x := by
  exact (((G.box b).flow.connection t).scalarCurvature_eq_of_local_isometry
    (G.connection t) isOpen_univ ((G.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => ((G.box b).metric_pullback t ht y v w).symm) (mem_univ x)).symm



theorem box_negativeCurvaturePart_pullback (G : GeneralizedRicciFlowData.{u})
    (b : G.box_index) (t : ℝ) (ht : t ∈ (G.box b).interval)
    (x : (G.box b).carrier.carrier) :
    (G.connection t).negativeCurvaturePart ((G.box b).forward t ht x) =
      ((G.box b).flow.connection t).negativeCurvaturePart x := by
  exact (negativeCurvaturePart_eq_of_local_isometry ((G.box b).flow.connection t)
    (G.connection t) isOpen_univ ((G.box b).forward_smooth t ht).contMDiffOn
    (fun y _ v w => ((G.box b).metric_pullback t ht y v w).symm) (mem_univ x)).symm



theorem terminal_box_hamiltonIvey_pinching
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (b : E.extended.box_index) (hT : T ∈ (E.extended.box b).interval)
    (x : (E.extended.box b).carrier.carrier) :
    -6 / (1 + 4 * T) ≤ ((E.extended.box b).flow.connection T).scalarCurvature x ∧
      (0 < ((E.extended.box b).flow.connection T).negativeCurvaturePart x →
        2 * ((E.extended.box b).flow.connection T).negativeCurvaturePart x *
          (Real.log (((E.extended.box b).flow.connection T).negativeCurvaturePart x) +
            Real.log (1 + T) - 3) ≤
          ((E.extended.box b).flow.connection T).scalarCurvature x) := by
  have hpos := terminalTime_pos H
  have hevent := terminal_box_eventually H E b hT
  have hfilter : 𝓝[<] T ≤ 𝓝[(E.extended.box b).interval] T :=
    nhdsWithin_le_iff.mpr (hevent.mono fun _ ht => ht.2)
  have hscalar := (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
    hM04 _ (E.extended.box b).flow x T hT).tendsto.mono_left hfilter
  have hnegative := (flow_negativeCurvaturePart_continuousOn
    (E.extended.box b).flow x T hT).tendsto.mono_left hfilter
  have htime : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
    continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · have hbarrier : Tendsto (fun t : ℝ => -6 / (1 + 4 * t)) (𝓝[<] T)
        (𝓝 (-6 / (1 + 4 * T))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add (htime.const_mul 4)) (by linarith)
    apply le_of_tendsto_of_tendsto hbarrier hscalar
    filter_upwards [hevent] with t ht
    have h := (extension_hamiltonIveyPinchedAt_old H E t ht.1).2.2.1
      ((E.extended.box b).forward t ht.2 x)
    simpa only [GeneralizedRicciFlowData.scalar, box_scalar_pullback] using h
  · intro hn
    have hlogtime : Tendsto (fun t : ℝ => Real.log (1 + t)) (𝓝[<] T)
        (𝓝 (Real.log (1 + T))) :=
      (tendsto_const_nhds.add htime).log (by linarith)
    have hmodel := (hnegative.const_mul 2).mul
      (((hnegative.log hn.ne').add hlogtime).sub (tendsto_const_nhds (x := (3 : ℝ))))
    apply le_of_tendsto_of_tendsto hmodel hscalar
    filter_upwards [hevent, hnegative.eventually (Ioi_mem_nhds hn)] with t ht hnt
    have h := (extension_hamiltonIveyPinchedAt_old H E t ht.1).2.2.2
      ((E.extended.box b).forward t ht.2 x)
    simp only [GeneralizedRicciFlowData.scalar, box_scalar_pullback,
      box_negativeCurvaturePart_pullback] at h
    exact h hnt



theorem extension_hamiltonIveyPinchedAt_terminal
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (hT : T ∈ E.extended.interval) : generalizedHamiltonIveyPinchedAt E.extended T := by
  refine ⟨hT, (terminalTime_pos H).le, ?_, ?_⟩
  · intro x
    obtain ⟨b, hb, y, rfl⟩ := E.extended.box_covers T x
    change -6 / (1 + 4 * T) ≤ (E.extended.connection T).scalarCurvature _
    rw [box_scalar_pullback]
    exact (terminal_box_hamiltonIvey_pinching hM04 H E b hb y).1
  · intro x
    obtain ⟨b, hb, y, rfl⟩ := E.extended.box_covers T x
    change 0 < (E.extended.connection T).negativeCurvaturePart _ → _
    rw [box_negativeCurvaturePart_pullback]
    change 0 < ((E.extended.box b).flow.connection T).negativeCurvaturePart y →
      _ ≤ (E.extended.connection T).scalarCurvature _
    rw [box_scalar_pullback]
    exact (terminal_box_hamiltonIvey_pinching hM04 H E b hb y).2



theorem extension_hamiltonIveyPinched
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T) :
    generalizedHamiltonIveyPinched E.extended := by
  intro t ht
  rcases E.times_subset ht with htold | htT
  · exact extension_hamiltonIveyPinchedAt_old H E t htold
  · have htT' : t = T := mem_singleton_iff.mp htT
    subst t
    exact extension_hamiltonIveyPinchedAt_terminal hM04 H E ht



theorem extension_pinchedOrNonnegative
    (hM04 : RicciFlowCurvatureTheory.{u})
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T) :
    generalizedPinchedOrNonnegative E.extended := by
  have hp := extension_hamiltonIveyPinched hM04 H E
  exact Or.inl ⟨fun t ht => (hp t ht).2.1, hp⟩

end PoincareConjecture.M32
