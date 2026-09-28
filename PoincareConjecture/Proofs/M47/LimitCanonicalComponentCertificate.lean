import PoincareConjecture.Proofs.M47.LimitCanonicalComponentDiameterMargin
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentTopology










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}}
  (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitCanonical_component_eventually_certificate
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa C : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification P.m04 G.limit kappa hkappa hnc).certificate.solution
    ∀ _N : M27CanonicalComponent K 0 C,
      ∀ᶠ k in atTop,
        let f := limitCanonicalPhysicalTerminalChart G F R k
        let g := M13.scaleSmoothMetric
          ((F (G.subsequence k)).metric
            ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
          (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
        let D := M13.scaleLeviCivitaData
          ((F (G.subsequence k)).connection
            ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
          (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
        ∃ Nphys : SingularCComponent g D C,
          Nphys.carrier = f.target ∧ f G.limit.base ∈ Nphys.carrier := by
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  dsimp only
  intro N
  obtain ⟨_a, _ha, _hsec, hsectional⟩ :=
    limitCanonical_component_eventually_sectional_fields G P F R hkappa hnc N
  filter_upwards [hsectional,
    limitCanonical_component_eventually_strict_diameters G P F R hkappa hnc N]
    with k hs hd
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let g : RiemannianMetric 3
      ((F (G.subsequence k)).slice
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).carrier :=
    M13.scaleSmoothMetric ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
      (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let D : LeviCivitaData g := M13.scaleLeviCivitaData
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  have hsource : f.source = univ :=
    (limitCanonicalPhysicalChart_source _ _ _ _ _ _).trans hs.1
  have hf : Continuous f :=
    continuousOn_univ.mp (hsource ▸ f.contMDiffOn_toFun.continuousOn)
  have himage : f '' univ = f.target := by
    simpa only [hsource] using f.toPartialEquiv.image_source_eq_target
  let Nphys : SingularCComponent g D C := {
    constant_pos := N.constant_pos
    basepoint := f G.limit.base
    carrier := f.target
    component_eq := hs.2.1
    compact := himage ▸ N.compact.image hf
    topology := by
      rcases N.topology with hK | hK
      · exact Or.inl ⟨limitCanonical_image_closed_certificate f hsource
          (Classical.choice hK) G.limit.base hs.2.1⟩
      · exact Or.inr ⟨limitCanonical_image_closed_certificate f hsource
          (Classical.choice hK) G.limit.base hs.2.1⟩
    positive_sectional := fun x hx u v huv => (hs.2.2.2 x hx u v huv).1
    sectional_lower := fun x hx u v huv => (hs.2.2.2 x hx u v huv).2
    diameter_lower := hd.2.2.1
    diameter_upper := hd.2.2.2
  }
  exact ⟨Nphys, rfl, f.map_source (hsource.symm ▸ mem_univ G.limit.base)⟩

end PoincareConjecture.M47
