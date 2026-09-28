import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Quotient.Coordinates










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

private theorem realProjectiveThree_t2Space : T2Space RealProjectiveThree := by
  have hq := Poincare.Topology.isOpenQuotientMap_of_pair_fibers
    realProjectiveThreeSetoid Neg.neg continuous_neg (fun _ _ => Iff.rfl)
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  have hrel : {z : UnitThreeSphere × UnitThreeSphere |
      Quotient.mk' z.1 = (Quotient.mk' z.2 : RealProjectiveThree)} =
      {z | z.1 = z.2} ∪ {z | z.1 = -z.2} := by
    ext z
    exact Quotient.eq
  rw [hrel]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst continuous_snd.neg)

theorem not_compactSpace_puncturedRealProjectiveThree (p : RealProjectiveThree) :
    ¬ CompactSpace (PuncturedRealProjectiveThree p) := by
  intro hc
  let : T2Space RealProjectiveThree := realProjectiveThree_t2Space
  have hcompact : IsCompact ({p}ᶜ : Set RealProjectiveThree) :=
    isCompact_iff_compactSpace.mpr hc
  have hopen : IsOpen ({p} : Set RealProjectiveThree) := by
    simpa using hcompact.isClosed.isOpen_compl
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective p
  have hpair : IsOpen ({v, -v} : Set UnitThreeSphere) := by
    convert hopen.preimage continuous_quotient_mk' using 1
    ext x
    simp only [mem_insert_iff, mem_singleton_iff, mem_preimage]
    exact (@Quotient.eq UnitThreeSphere realProjectiveThreeSetoid x v).symm
  have hv : v ≠ -v := ne_neg_of_mem_unit_sphere ℝ v
  have hdiff : ({v, -v} : Set UnitThreeSphere) \ {-v} = {v} := by
    ext x
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hn⟩
      exact hx.resolve_right hn
    · intro hx
      exact ⟨Or.inl hx, fun hn => hv (hx.symm.trans hn)⟩
  have hsingle : IsOpen ({v} : Set UnitThreeSphere) :=
    hdiff ▸ hpair.inter isClosed_singleton.isOpen_compl
  let : ConnectedSpace UnitThreeSphere :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  have hfull : ({v} : Set UnitThreeSphere) = univ :=
    (show IsClopen ({v} : Set UnitThreeSphere) from
      ⟨isClosed_singleton, hsingle⟩).eq_univ (singleton_nonempty v)
  have hneg : -v ∈ ({v} : Set UnitThreeSphere) := hfull.symm ▸ mem_univ (-v)
  exact hv hneg.symm

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]


theorem CapModelEquivalence.not_isCompact_carrier {kind : CapModelKind}
    {p : RealProjectiveThree} {carrier : Set M}
    (model : CapModelEquivalence kind p carrier) : ¬ IsCompact carrier := by
  intro hc
  let : TopologicalSpace model.model := model.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) model.model := model.model_charted
  let : IsManifold (𝓡 3) ∞ model.model := model.model_manifold
  have himage : model.forward '' carrier = univ := by
    apply eq_univ_of_forall
    intro y
    exact ⟨model.inverse y, model.inverse_mem y, model.right_inverse y⟩
  have hmodel : IsCompact (univ : Set model.model) := by
    rw [← himage]
    exact hc.image_of_continuousOn model.forward_smooth.continuousOn
  let : CompactSpace model.model := isCompact_univ_iff.mp hmodel
  cases kind with
  | euclidean =>
    let : CompactSpace (EuclideanSpace ℝ (Fin 3)) :=
      (model.standard_model.trans Homeomorph.ulift).compactSpace
    exact noncompact_univ (EuclideanSpace ℝ (Fin 3)) isCompact_univ
  | puncturedProjective =>
    exact not_compactSpace_puncturedRealProjectiveThree p
      (model.standard_model.trans Homeomorph.ulift).compactSpace

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

omit [T2Space M] in

theorem CapCertificate.not_isCompact_carrier {g : RiemannianMetric 3 M}
    (C : CapCertificate g) : ¬ IsCompact C.carrier :=
  C.model_equivalence.not_isCompact_carrier

end PoincareConjecture
