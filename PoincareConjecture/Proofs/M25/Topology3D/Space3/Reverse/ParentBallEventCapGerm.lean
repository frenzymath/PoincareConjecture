import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallDiscExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapGermCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventContainment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapNormalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapCoordinates

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem RegularSurgeryEvent.exists_canonical_cap_parameter_alignment
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (j : Fin 2)
    (A : BallNeighborhoodChart E3 E3)
    (hboundary : A.boundary = E.child j '' (univ ×ˢ ({0} : Set ℝ)))
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (hnormalized : A.chart ''
      {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} = (E.newCap j).cap) :
    ∃ g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      (∀ q : UnitTwoSphere, A.chart (g q : E3) = E.child j (q, 0)) ∧
      let Q := nativeCapSourceChart (E.child j) u (E.newCap j) a ha g
      let M := E.canonicalCapBall j
      let Da := {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2}
      ∃ R : ℝ, 1 < R ∧ closedBall (0 : E2) R ⊆ Q.source ∧
        Q '' closedBall (0 : E2) 1 =
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
        (∀ X : E2, ‖X‖ ≤ R →
          (heightCoordinates (Q X : E3)).2 < (E.newCap j).overlapWidth) ∧
        ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          (∀ y : E3, ‖G y‖ = ‖y‖) ∧
          (∀ X : E2, ‖X‖ ≤ R → G (referenceCapPoint a X) = (Q X : E3)) ∧
          G '' Da = ((↑) : UnitTwoSphere → E3) ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
          ∃ B : BallNeighborhoodChart E3 E3,
            B.chart = G.toHomeomorph.toOpenPartialHomeomorph.trans M.chart ∧
            B.chart.source = G ⁻¹' M.chart.source ∧ B.chart.target = M.chart.target ∧
            (∀ y : E3, B.chart y = M.chart (G y)) ∧
            (∀ Y : E3, B.chart.symm Y = G.symm (M.chart.symm Y)) ∧
            B.inside = M.inside ∧ B.closedRegion = M.closedRegion ∧
            B.boundary = M.boundary ∧
            (∀ X : E2, ‖X‖ ≤ R →
              B.chart (referenceCapPoint a X) = A.chart (referenceCapPoint a X)) ∧
            B.chart '' Da = (E.newCap j).cap := by
  obtain ⟨g, hg⟩ :=
    exists_ball_boundary_parametrization (E.child j) (E.child_embedding j) A hboundary
  let P := referenceCapSphereChart a ha
  let Q := nativeCapSourceChart (E.child j) u (E.newCap j) a ha g
  let M := E.canonicalCapBall j
  let Da := {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2}
  obtain ⟨hPs, _hPt, hPpoint, _hPi, hPsm, hPism, _hPimage⟩ :=
    referenceCapSphereChart_spec a ha
  obtain ⟨_hQs, _hQt, _hQf, _hQi, hQsm, hQism, hQclosed, hQimage,
      R₀, hR₀, hR₀source, hR₀height, hR₀match⟩ :=
    nativeCapSourceChart_spec (E.child j) u (E.newCap j) A a ha g hg hnormalized
  have hPclosed : closedBall (0 : E2) 1 ⊆ P.source := by rw [hPs]; exact subset_univ _
  obtain ⟨R₁, hR₁, _hR₁source, G, hG, hGpoint⟩ :=
    exists_sphere_disc_pointwise_extension P Q hPclosed hQclosed hPsm hPism hQsm hQism
  let R := min R₀ R₁
  have hR : 1 < R := lt_min hR₀ hR₁
  have hRsource : closedBall (0 : E2) R ⊆ Q.source :=
    fun X hX => hR₀source (mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hX).trans (min_le_left _ _)))
  have hGref (X : E2) (hX : ‖X‖ ≤ R) :
      G (referenceCapPoint a X) = (Q X : E3) := by
    rw [← hPpoint X]
    exact hGpoint X (hX.trans (min_le_right _ _))
  have hGimage : G '' Da = ((↑) : UnitTwoSphere → E3) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    change G '' {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} = _
    rw [← referenceCapPoint_image_closedBall a ha, ← hQimage]
    simp only [image_image]
    exact image_congr (fun X hX => hGref X ((mem_closedBall_zero_iff.mp hX).trans hR.le))
  have hGsym (y : E3) : ‖G.symm y‖ = ‖y‖ := by
    rw [← hG (G.symm y), G.apply_symm_apply]
  let B := M.normReparametrize G.symm hGsym
  have hBs : B.chart.source = G ⁻¹' M.chart.source := by
    ext y
    change (y ∈ (univ : Set E3) ∧ G y ∈ M.chart.source) ↔ G y ∈ M.chart.source
    simp only [mem_univ, true_and]
  have hBt : B.chart.target = M.chart.target := by
    ext Y
    change (Y ∈ M.chart.target ∧ M.chart.symm Y ∈ (univ : Set E3)) ↔ Y ∈ M.chart.target
    simp only [mem_univ, and_true]
  obtain ⟨_hMc, _hMs, _hMt, _hMf, _hMi, hMq, _hMrest⟩ := E.canonicalCapBall_spec j
  obtain ⟨hProfile, hTube, hHeight, hRemoval, hScale, hSign⟩ := E.newCap_spec j
  have hMtag (q : UnitTwoSphere) : M.chart (q : E3) =
      (E.newCap j).profile.capMap (E.newCap j).tube (E.newCap j).cutHeight
        (E.newCap j).sign (E.newCap j).removal (E.newCap j).scale q := by
    rw [hProfile, hTube, hHeight, hRemoval, hScale, hSign]
    exact hMq q
  have hBpatch (X : E2) (hX : ‖X‖ ≤ R) :
      B.chart (referenceCapPoint a X) = A.chart (referenceCapPoint a X) := by
    change M.chart (G (referenceCapPoint a X)) = _
    rw [hGref X hX, hMtag]
    exact hR₀match X (hX.trans (min_le_left _ _))
  refine ⟨g, hg, R, hR, hRsource, hQimage,
    fun X hX => hR₀height X (hX.trans (min_le_left _ _)),
    G, hG, hGref, hGimage, B, rfl, hBs, hBt, fun _ => rfl, fun _ => rfl,
    M.normReparametrize_inside G.symm hGsym,
    M.normReparametrize_closedRegion G.symm hGsym,
    M.normReparametrize_boundary G.symm hGsym, hBpatch, ?_⟩
  rw [← hnormalized]
  apply image_congr
  intro y hy
  obtain ⟨X, hX, rfl⟩ : y ∈ referenceCapPoint a '' closedBall (0 : E2) 1 := by
    rwa [referenceCapPoint_image_closedBall a ha]
  exact hBpatch X ((mem_closedBall_zero_iff.mp hX).trans hR.le)

theorem RegularSurgeryEvent.exists_common_cap_ball_charts
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (A : Fin 2 → BallNeighborhoodChart E3 E3)
    (hboundary : ∀ j : Fin 2,
      (A j).boundary = E.child j '' (univ ×ˢ ({0} : Set ℝ))) :
    ∃ i : Fin 2,
      let j : Fin 2 := ![1, 0] i
      let M := E.canonicalCapBall j
      (Disjoint (A i).closedRegion (A j).closedRegion ∨
        (A j).closedRegion ⊆ (A i).inside) ∧
      ∃ a : ℝ, ∃ ha : a ∈ Ioo (1 / 2 : ℝ) 1,
        ∃ N : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        ∃ hN : (∀ y : E3, ‖N y‖ = ‖y‖),
          let Abar := (A j).normReparametrize N hN
          let Da := {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2}
          Abar.chart '' Da = (E.newCap j).cap ∧
          ∃ g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
            (∀ q : UnitTwoSphere, Abar.chart (g q : E3) = E.child j (q, 0)) ∧
            let Q := nativeCapSourceChart (E.child j) u (E.newCap j) a ha g
            ∃ R : ℝ, 1 < R ∧ closedBall (0 : E2) R ⊆ Q.source ∧
              (∀ X : E2, ‖X‖ ≤ R →
                (heightCoordinates (Q X : E3)).2 < (E.newCap j).overlapWidth) ∧
              ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
                (∀ y : E3, ‖G y‖ = ‖y‖) ∧
                (∀ X : E2, ‖X‖ ≤ R →
                  G (referenceCapPoint a X) = (Q X : E3)) ∧
                G '' Da = ((↑) : UnitTwoSphere → E3) ''
                  {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
                ∃ B : BallNeighborhoodChart E3 E3,
                  B.chart = G.toHomeomorph.toOpenPartialHomeomorph.trans M.chart ∧
                  B.inside = M.inside ∧ B.closedRegion = M.closedRegion ∧
                  B.boundary = M.boundary ∧ B.chart '' Da = (E.newCap j).cap ∧
                  ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
                    (∀ y ∈ sphere (0 : E3) 1, F y = y) ∧
                    F '' ball (0 : E3) 1 = ball 0 1 ∧
                    F '' closedBall (0 : E3) 1 = closedBall 0 1 ∧
                    ∃ A' : BallNeighborhoodChart E3 E3,
                      A'.chart = F.toHomeomorph.toOpenPartialHomeomorph.trans Abar.chart ∧
                      A'.inside = (A j).inside ∧ A'.closedRegion = (A j).closedRegion ∧
                      A'.boundary = (A j).boundary ∧
                      (∀ y ∈ sphere (0 : E3) 1, A'.chart y = Abar.chart y) ∧
                      (∀ q : UnitTwoSphere,
                        A'.chart (g q : E3) = E.child j (q, 0)) ∧
                      A'.chart '' Da = (E.newCap j).cap ∧
                      B.closedRegion ⊆ A'.closedRegion ∧
                      ∀ᶠ y in 𝓝ˢ Da,
                        y ∈ A'.chart.source ∧ y ∈ B.chart.source ∧
                          A'.chart y = B.chart y := by
  obtain ⟨i, hregions, _haxis, _side, _hside, _hin, _hout, _hsign, _hMin, hMclosed⟩ :=
    E.exists_canonical_child_containment A hboundary
  let j : Fin 2 := ![1, 0] i
  let M := E.canonicalCapBall j
  obtain ⟨a, ha, N, hN, _hAc, _hAs, _hAt, _hAf, _hAi,
      hAinside, hAclosed, hAboundary, hAcap⟩ :=
    exists_normalized_child_cap_ball (E.child j) (E.child_embedding j) u (E.newCap j)
      (A j) (hboundary j)
  let Abar := (A j).normReparametrize N hN
  let Da := {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2}
  obtain ⟨g, hg, R, hR, hRsource, _hQimage, hRheight, G, hG, hGpoint, hGimage,
      B, hBc, _hBs, _hBt, _hBf, _hBi, hBinside, hBclosed, hBboundary,
      hBpatch, hBcap⟩ :=
    E.exists_canonical_cap_parameter_alignment j Abar (hAboundary.trans (hboundary j))
      a ha hAcap
  let P := referenceCapSphereChart a ha
  obtain ⟨hPs, _hPt, hPpoint, _hPi, _hPsm, _hPism, _hPimage⟩ :=
    referenceCapSphereChart_spec a ha
  let V := P '' ball (0 : E2) R
  have hV : IsOpen V := P.isOpen_image_of_subset_source isOpen_ball
    (by rw [hPs]; exact subset_univ _)
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have hDaS : Da ⊆ sphere (0 : E3) 1 :=
    fun _ hy => mem_sphere_zero_iff_norm.mpr hy.1
  have hDaU : Da ⊆ U := by
    intro y hy
    let q : UnitTwoSphere := ⟨y, hDaS hy⟩
    have hqV : q ∈ V := by
      obtain ⟨X, hX, hxy⟩ : y ∈ referenceCapPoint a '' closedBall (0 : E2) 1 := by
        rwa [referenceCapPoint_image_closedBall a ha]
      refine ⟨X, mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hX).trans_lt hR), ?_⟩
      exact Subtype.ext ((hPpoint X).trans hxy)
    change q ∈ ((↑) : UnitTwoSphere → E3) ⁻¹' U
    rwa [hUV]
  have hpatch (y : E3) (hyU : y ∈ U) (hy : ‖y‖ = 1) :
      Abar.chart y = B.chart y := by
    let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
    have hqV : q ∈ V := by rw [← hUV]; exact hyU
    obtain ⟨X, hX, hXq⟩ := hqV
    have hxy : referenceCapPoint a X = y :=
      (hPpoint X).symm.trans (congrArg (fun q : UnitTwoSphere => (q : E3)) hXq)
    rw [← hxy]
    exact (hBpatch X (mem_ball_zero_iff.mp hX).le).symm
  have hDa : IsCompact Da := (isCompact_sphere (0 : E3) 1).of_isClosed_subset
    ((isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_const heightCoordinates.continuous.snd)) hDaS
  have hBA : B.closedRegion ⊆ Abar.closedRegion := by
    rw [hBclosed, hAclosed]
    exact hMclosed
  obtain ⟨F, hFfix, hFball, hFclosed, _hFgerm, A', hA'c, _hA's, _hA't,
      _hA'f, _hA'i, hA'inside, hA'closed, hA'boundary, hA'point, hgerm⟩ :=
    exists_ball_chart_common_germ_of_sphere_patch Abar B hDa hDaS hU hDaU hpatch hBA
  refine ⟨i, hregions, a, ha, N, hN, hAcap, g, hg, R, hR, hRsource, hRheight,
    G, hG, hGpoint, hGimage, B, hBc, hBinside, hBclosed, hBboundary, hBcap,
    F, hFfix, hFball, hFclosed, A', hA'c, hA'inside.trans hAinside,
    hA'closed.trans hAclosed, hA'boundary.trans hAboundary, hA'point,
    ?_, ?_, ?_, hgerm⟩
  · intro q
    rw [hA'point _ (g q).property]
    exact hg q
  · rw [← hAcap]
    exact image_congr (fun y hy => hA'point y (hDaS hy))
  · rw [hA'closed]
    exact hBA

end PoincareConjecture.M25.Topology3D
