import PoincareConjecture.Proofs.M25.AppA_21_Local
import PoincareConjecture.Proofs.M25.AppA_21_Local.CappedCoreComponent
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCoreCarrierCollision
import PoincareConjecture.Proofs.M25.AppA_21_Local.SecondOverlapCylinder
import PoincareConjecture.Proofs.M25.AppA_21_Local.DoubleCappedTubePacking
import PoincareConjecture.Proofs.M25.AppA_21_Local.ClosedRegionAssembly
import PoincareConjecture.Proofs.M25.AppA_21_Local.FiniteCappedChainAmbientChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapDispatch
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapPullback

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M25

theorem finiteCappedLocalInput_of_services
    (hS : PoincareConjecture.M25.Topology3D.SchoenfliesService)
    (hD : PoincareConjecture.M25.Topology3D.DiffSphereIsotopyService) :
    FiniteCappedLocalInput.{u} := by
  classical
  obtain ⟨epsilonCC, hCCpos, hCCcap, hCC⟩ :=
    ConnectedNeckCapCover.exists_repairedData_or_compact_capped_core_component.{u}
  obtain ⟨epsilonCA, hCApos, _, hCA⟩ :=
    CapCertificate.exists_two_cap_component_or_disjoint_core_carrier.{u}
  obtain ⟨epsilonOverlap, hOverlapPos, _, hOverlap⟩ :=
    L3a_second_overlap_cylinder_model.{u}
  obtain ⟨epsilonPacking, hPackingPos, _, hPacking⟩ :=
    L3_doubleCappedTube_of_disjoint_core_carrier.{u}
  obtain ⟨epsilonChart, hChartPos, _, hChart⟩ :=
    CapCertificate.exists_finite_chain_ambient_chart.{u}
  refine ⟨min epsilonCC (min epsilonCA (min epsilonOverlap (min epsilonPacking epsilonChart))),
    lt_min hCCpos (lt_min hCApos (lt_min hOverlapPos (lt_min hPackingPos hChartPos))),
    (min_le_left _ _).trans hCCcap, ?_⟩
  intro M _ _ _ _ _ _ g H hepsilon x hx hfinite
  have heCC : H.epsilon ≤ epsilonCC := hepsilon.trans (min_le_left _ _)
  have heCA : H.epsilon ≤ epsilonCA :=
    hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heOverlap : H.epsilon ≤ epsilonOverlap :=
    hepsilon.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hePacking : H.epsilon ≤ epsilonPacking :=
    hepsilon.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have heChart : H.epsilon ≤ epsilonChart :=
    hepsilon.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨Cseed, hCseed, hxseed, _⟩ := hfinite
  rcases hCC H heCC x hx ⟨Cseed, hCseed, hxseed⟩ with hdata | htuple
  · exact hdata
  obtain ⟨C0, hC0, _hx0, hno, b, D, _hb, hshape, _hsource, hstart,
    hsep, hcenters, hquarters, _hincidence, K, hKcap, hKeps, _hKchain,
    hKtube, hKcarrier, C1, hC1, y, _hyX, hycore, hyout, hyclosure, hmeet, hW⟩ := htuple
  have hW' : H.X ⊆ K.carrier ∪ C1.carrier ∧
      IsCompact (K.carrier ∪ C1.carrier) ∧ IsClopen (K.carrier ∪ C1.carrier) ∧
      IsConnected (K.carrier ∪ C1.carrier) ∧
      ∃ z : M, K.carrier ∪ C1.carrier = connectedComponent z := hW
  obtain ⟨hXW, hWcompact, _hWclopen, hWconnected, _hWcomponent⟩ := hW'
  have hC0e : C0.epsilon = H.epsilon := H.cap_epsilon C0 hC0
  have hC1e : C1.epsilon = H.epsilon := H.cap_epsilon C1 hC1
  have hC10e : C1.epsilon = C0.epsilon := hC1e.trans hC0e.symm
  have heCA0 : C0.epsilon ≤ epsilonCA := by
    rw [hC0e]
    exact heCA
  have heOverlap0 : C0.epsilon ≤ epsilonOverlap := by
    rw [hC0e]
    exact heOverlap
  have heChart0 : C0.epsilon ≤ epsilonChart := by
    rw [hC0e]
    exact heChart
  have hno' : ¬ (C0.carrier \ C0.end_neck.region
      (C0.epsilon⁻¹ / 2) C0.epsilon⁻¹ ⊆ C1.core) := by
    simpa only [hC0e] using hno C1 hC1
  have hout : ∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C0.carrier :=
    fun i hi hpos => (hcenters i hi hpos).2
  have hC0sub : C0.carrier ⊆ K.carrier := by
    simpa only [hKcap] using K.cap_subset
  have halt := hCA C0 C1 heCA0 hC10e hno' K.carrier
    K.connected.isPreconnected hC0sub y hycore hyout
  dsimp only at halt
  rcases halt with ⟨hWeq, hWc, _hWopen, _hWconn, _hWcomp⟩ | hdisjoint
  · have hcompactCaps : IsCompact (C0.carrier ∪ C1.carrier) := by
      rw [← hWeq]
      exact hWc
    obtain ⟨kind, hcertificate⟩ :=
      Topology3D.closedModelCapData_exists_closed_component_of_services hS hD
        (Topology3D.ClosedModelCapData.ofCapCertificate C0)
        (Topology3D.ClosedModelCapData.ofCapCertificate C1) hcompactCaps
    have hcomponent :
        Nonempty (ClosedComponentCertificate kind (C0.carrier ∪ C1.carrier)) :=
      hcertificate
    have hcontains : H.X ⊆ C0.carrier ∪ C1.carrier := by
      rw [← hWeq]
      exact hXW
    exact PoincareConjecture.repairedData_of_two_cap_component H C0 C1 kind hcomponent hcontains
      hC0e hC1e (H.cap_constant_bound C0 hC0) (H.cap_constant_bound C1 hC1)
  · have hcyl := hOverlap C0 C1 D heOverlap0 hC10e hshape hstart hsep hout hquarters
      hno' K hKcap hKtube hdisjoint y hycore hyclosure hyout hmeet hWcompact
    obtain ⟨Dc, hcap0, hcap1, hDtube, hDcarrier⟩ :=
      hPacking H hePacking C0 C1 D hC0 hC1 hshape hstart hsep hout hquarters hno'
        K hKcap hKeps hKtube hKcarrier hdisjoint y hycore hyclosure hyout hmeet
        hWcompact hWconnected hcyl
    obtain ⟨Phi, hPhiSource, hPhiTarget, hPhiSmooth, hPhiInverse, _hfix, _hfixSymm⟩ :=
      hChart C0 D hshape heChart0 hstart hsep hout
    have hPhiSource' : Phi.source = K.carrier := hPhiSource.trans hKcarrier.symm
    have hPhiSmooth' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi K.carrier := by
      rw [hKcarrier]
      exact hPhiSmooth
    let A0 := Topology3D.ClosedModelCapData.ofCapCertificate C0
    let A1 := Topology3D.ClosedModelCapData.ofCapCertificate C1
    obtain ⟨B, hBcarrier, _hBepsilon, _hBkind, _hBpuncture⟩ :=
      A0.exists_pullback K.carrier Phi hPhiSource' hPhiTarget hPhiSmooth' hPhiInverse
    have hcompactLight : IsCompact (B.carrier ∪ A1.carrier) := by
      change IsCompact (B.carrier ∪ C1.carrier)
      rw [hBcarrier]
      exact hWcompact
    obtain ⟨kind, hclassified⟩ :=
      Topology3D.closedModelCapData_exists_closed_component_of_services hS hD B A1 hcompactLight
    change Nonempty (ClosedComponentCertificate kind (B.carrier ∪ C1.carrier)) at hclassified
    rw [hBcarrier] at hclassified
    have hcomponent : Nonempty (ClosedComponentCertificate kind Dc.carrier) := by
      rw [hDcarrier]
      exact hclassified
    have hcontains : H.X ⊆ Dc.carrier := by
      rw [hDcarrier]
      exact hXW
    refine PoincareConjecture.repairedData_of_double_capped_tube_component H Dc kind hcomponent
      hcontains ?_ ?_ hDtube ?_ ?_
    · rw [hcap0]
      exact hC0e
    · rw [hcap1]
      exact hC1e
    · rw [hcap0]
      exact H.cap_constant_bound C0 hC0
    · rw [hcap1]
      exact H.cap_constant_bound C1 hC1

end PoincareConjecture.M25
