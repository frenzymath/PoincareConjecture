import PoincareConjecture.Proofs.M35.Thm12_28.LimitProjective
import PoincareConjecture.Proofs.M35.Thm12_28.LimitNoncompact
import PoincareConjecture.Proofs.M35.Thm12_28.CapCompactness
import PoincareConjecture.Proofs.M35.Thm12_28.NeckCompactness











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



theorem blowupSequence_limit_not_projective (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier :=
      L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ¬Nonempty (M27ProjectivePlaneLineFlowCertificate A.solution) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  rintro ⟨K⟩
  apply blowupSequence_limit_no_antipodal_product P E t x ht hR L K.cover
    K.cover_local_diffeomorph
  intro p
  exact ((K.cover_fibers p (-p.1, p.2)).mpr (Or.inr rfl)).symm




theorem exists_limit_cap_or_neck_constants (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∃ C : ℝ, 0 < C ∧ ∀ (g₀ : StandardInitialMetric)
        (E : RepairedStandardCapExistenceData g₀)
        (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
        (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
        (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
        (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
          (blowupBackwardInterval ⊤)) (kappa : ℝ)
        (A : BlowupAncientKappaIdentification L.limit kappa),
        letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
        letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
        letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
          L.limit.carrier.chartedSpace
        letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
        letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
        letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
        letI : SecondCountableTopology L.limit.carrier.carrier :=
          L.limit.carrier.secondCountable
        letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
        ∀ s : ℝ, s ≤ 0 → ∀ y : L.limit.carrier.carrier,
          (∃ N : StrongEvolvingNeck A.solution s epsilon,
            N.center = y ∧ ∃ j : ℕ,
              closure N.terminal_neck.carrier ⊆ L.exhaustion.space j) ∨
          (∃ N : M27CanonicalCap A.solution s y epsilon C, ∃ j : ℕ,
            closure N.cap.carrier ⊆ L.exhaustion.space j) := by
  obtain ⟨delta, hdelta, hmodels⟩ := P.kappa_models.corollary_9_94
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon he hdeltae
  obtain ⟨C, hC, hcanonical⟩ := hmodels epsilon he hdeltae
  refine ⟨C, hC, ?_⟩
  intro g₀ E t x ht hR L kappa A
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro s hs y
  have hnot := blowupSequence_limit_not_projective P E t x ht hR L A
  have hnoncompact := blowupSequence_limit_noncompact P E t x ht hR L
  have hcover (z : L.limit.carrier.carrier) : z ∈ ⋃ i, L.exhaustion.space i :=
    (congrArg (fun U : Set L.limit.sliceCarrier.carrier => z ∈ U)
      L.exhaustion.space_covers).mpr (mem_univ z)
  cases hcanonical A.solution hnot s hs y with
  | neck N hcenter =>
      have hc := N.terminal_neck.isCompact_closure (A.solution.complete s hs)
      obtain ⟨j, hj⟩ := hc.elim_directed_cover L.exhaustion.space
        L.exhaustion.space_open (fun z _ => hcover z)
        (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
          L.exhaustion.space_increasing (le_max_right _ _)⟩)
      exact Or.inl ⟨N, hcenter, j, hj⟩
  | cap N =>
      have hc := N.cap.isCompact_closure (A.solution.complete s hs)
      obtain ⟨j, hj⟩ := hc.elim_directed_cover L.exhaustion.space
        L.exhaustion.space_open (fun z _ => hcover z)
        (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
          L.exhaustion.space_increasing (le_max_right _ _)⟩)
      exact Or.inr ⟨N, j, hj⟩
  | component N => exact (hnoncompact N.compact).elim
  | round N => exact (hnoncompact N.compact).elim

end PoincareConjecture.M35.OrdinaryRealization
