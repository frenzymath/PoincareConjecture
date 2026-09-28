import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereJetMargin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_AxialJetMargin











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M47

open M44 SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance componentJetCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance componentJetCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance componentJetTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance componentJetTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace



def limitCanonicalSectionalJetRegion (a : ℝ) :
    Set (MetricTwoJet 3 × (E × E)) :=
  {p | p.1 ∈ sectionalJetLowerRegion a p.2.1 p.2.2}



theorem limitCanonical_isOpen_sectional_jet_region (a : ℝ) :
    IsOpen (limitCanonicalSectionalJetRegion a) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨J, u, v⟩ hJ
  have hgram : Continuous (fun p : MetricTwoJet 3 × (E × E) =>
      collarJetGram p.2.1 p.2.2 p.1) := by
    unfold collarJetGram
    fun_prop
  have hcurv := continuousAt_jetCurvature_family
    (continuousAt_fst (p := (J, (u, v)))) hJ.1
    continuousAt_snd.fst continuousAt_snd.snd
    continuousAt_snd.fst continuousAt_snd.snd
  have hmargin : 0 < jetCurvature J u v u v - a * collarJetGram u v J :=
    sub_pos.mpr hJ.2.2
  filter_upwards [continuousAt_fst.eventually
    ((isOpen_ricciFlowOperator_domain 3).mem_nhds hJ.1),
    hgram.continuousAt.eventually (lt_mem_nhds hJ.2.1),
    (hcurv.sub (continuousAt_const.mul hgram.continuousAt)).eventually
      (lt_mem_nhds hmargin)] with p hinv hpos hbound
  exact ⟨hinv, hpos, sub_pos.mp hbound⟩





theorem limitCanonical_exists_uniform_sectional_jet_margin
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {P : Set (E × E)} (hP : IsCompact P)
    (J0 : X → MetricTwoJet 3) (hJ0 : ContinuousOn J0 K) (a : ℝ)
    (hmargin : ∀ x ∈ K, ∀ p ∈ P,
      J0 x ∈ sectionalJetLowerRegion a p.1 p.2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x ∈ K, ∀ p ∈ P,
      ∀ J : MetricTwoJet 3, ‖J - J0 x‖ ≤ delta →
        J ∈ sectionalJetLowerRegion a p.1 p.2 := by
  let L : Set (MetricTwoJet 3 × (E × E)) :=
    (fun p : X × (E × E) => (J0 p.1, p.2)) '' (K ×ˢ P)
  have hJ : ContinuousOn (fun p : X × (E × E) => J0 p.1) (K ×ˢ P) :=
    hJ0.comp continuousOn_fst (fun _ hp => hp.1)
  have hL : IsCompact L :=
    (hK.prod hP).image_of_continuousOn (hJ.prodMk continuousOn_snd)
  have hsub : L ⊆ limitCanonicalSectionalJetRegion a := by
    rintro _ ⟨⟨x, p⟩, ⟨hx, hp⟩, rfl⟩
    exact hmargin x hx p hp
  obtain ⟨delta, hdelta, hinside⟩ := hL.exists_cthickening_subset_open
    (limitCanonical_isOpen_sectional_jet_region a) hsub
  refine ⟨delta, hdelta, ?_⟩
  intro x hx p hp J hnear
  change (J, p) ∈ limitCanonicalSectionalJetRegion a
  apply hinside
  apply Metric.mem_cthickening_of_dist_le (J, p) (J0 x, p) delta L
    (show (J0 x, p) ∈ L from ⟨(x, p), ⟨hx, hp⟩, rfl⟩)
  rw [dist_eq_norm]
  change max ‖J - J0 x‖ ‖p - p‖ ≤ delta
  simpa only [sub_self, norm_zero, max_eq_left (norm_nonneg _)] using hnear

end PoincareConjecture.M47
